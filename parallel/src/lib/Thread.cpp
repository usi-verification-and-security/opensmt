//
// Created by Matteo Marescotti on 02/12/15.
//

#include "Thread.h"

extern "C" {
#include <errno.h>
}


#ifdef __APPLE__

#define __unused __attribute__((unused))

int
pthread_barrierattr_init(pthread_barrierattr_t *attr __unused) {
    return 0;
}

int
pthread_barrierattr_destroy(pthread_barrierattr_t *attr __unused) {
    return 0;
}

int
pthread_barrierattr_getpshared(const pthread_barrierattr_t *attr __unused,
                               int *pshared) {
    *pshared = PTHREAD_PROCESS_PRIVATE;
    return 0;
}

int
pthread_barrierattr_setpshared(pthread_barrierattr_t *attr __unused,
                               int pshared) {
    if (pshared != PTHREAD_PROCESS_PRIVATE) {
        errno = EINVAL;
        return -1;
    }
    return 0;
}

int
pthread_barrier_init(pthread_barrier_t *barrier,
                     const pthread_barrierattr_t *attr __unused,
                     unsigned count) {
    if (count == 0) {
        errno = EINVAL;
        return -1;
    }

    if (pthread_mutex_init(&barrier->mutex, 0) < 0) {
        return -1;
    }
    if (pthread_cond_init(&barrier->cond, 0) < 0) {
        int errno_save = errno;
        pthread_mutex_destroy(&barrier->mutex);
        errno = errno_save;
        return -1;
    }

    barrier->limit = count;
    barrier->count = 0;
    barrier->phase = 0;

    return 0;
}

int
pthread_barrier_destroy(pthread_barrier_t *barrier) {
    pthread_mutex_destroy(&barrier->mutex);
    pthread_cond_destroy(&barrier->cond);
    return 0;
}

int
pthread_barrier_wait(pthread_barrier_t *barrier) {
    pthread_mutex_lock(&barrier->mutex);
    barrier->count++;
    if (barrier->count >= barrier->limit) {
        barrier->phase++;
        barrier->count = 0;
        pthread_cond_broadcast(&barrier->cond);
        pthread_mutex_unlock(&barrier->mutex);
        return PTHREAD_BARRIER_SERIAL_THREAD;
    } else {
        unsigned phase = barrier->phase;
        do
            pthread_cond_wait(&barrier->cond, &barrier->mutex);
        while (phase == barrier->phase);
        pthread_mutex_unlock(&barrier->mutex);
        return 0;
    }
}

#endif /* __APPLE__ */

Thread::Thread() :
        thread(nullptr), piper(Pipe()), pipew(Pipe()), stop_requested(false) { }

Thread::~Thread() {
    this->stop();
    this->join();
    delete this->thread;
    this->thread = nullptr;
}

void Thread::thread_wrapper() {
    try {
        pthread_barrier_wait(&this->barrier);
        this->main();
    }
    catch (const std::exception &e) {
        std::cout << "Unhandled exception on thread " << pthread_self() << ": " << e.what() << "\n";
    }
    catch (...) {
        std::cout << "Unhandled unknown exception on thread " << pthread_self() << "\n";
    }
    this->stop();
}

void Thread::start() {
    if (this->thread != nullptr)
        return;
    pthread_barrier_init(&this->barrier, nullptr, 2);
    this->thread = new std::thread(&Thread::thread_wrapper, this);
    pthread_barrier_wait(&this->barrier);
}

void Thread::stop() {
    this->mtx.lock();
    if (!this->joinable() || this->stop_requested) {
        this->mtx.unlock();
        return;
    }
    this->stop_requested = true;
    pthread_cancel(this->thread->native_handle());
    this->mtx.unlock();
}

void Thread::join() {
    if (this->joinable()) {
        this->thread->join();
        pthread_barrier_destroy(&this->barrier);
    }
}

bool Thread::joinable() {
    return this->thread != nullptr && this->thread->joinable();
}

Socket *Thread::reader() {
    return (pthread_self() == this->thread->native_handle()) ? this->piper.reader() : this->pipew.reader();
}

Socket *Thread::writer() {
    return (pthread_self() == this->thread->native_handle()) ? this->pipew.writer() : this->piper.writer();
}
