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


pthread_t Thread::init() {
    std::signal(SIGUSR1, [](int signal) {
        if (pthread_self() != Thread::main_thread)
            throw StopException();
    });
    return pthread_self();
}

pthread_t Thread::main_thread = Thread::init();

Thread::Thread() :
        thread(NULL), piper(Pipe::New()), pipew(Pipe::New()), stop_requested(false) {
    pthread_barrier_init(&this->barrier, NULL, 2);
}

Thread::~Thread() {
    pthread_barrier_destroy(&this->barrier);
    this->stop();
    this->join();
    delete this->thread;
}

void Thread::thread_wrapper() {
    try {
        pthread_barrier_wait(&this->barrier);
        this->main();
        return;
    } catch (StopException) { }
}

void Thread::start() {
    if (this->thread != NULL)
        return;
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
    this->mtx.unlock();
    if (pthread_self() != this->thread->native_handle())
        pthread_kill(this->thread->native_handle(), SIGUSR1);
    else
        throw StopException();
}

void Thread::join() {
    if (this->joinable())
        this->thread->join();
}

bool Thread::joinable() {
    return this->thread != NULL && this->thread->joinable();
}

Frame &Thread::reader() {
    return (pthread_self() == this->thread->native_handle()) ? this->piper.reader() : this->pipew.reader();
}

Frame &Thread::writer() {
    return (pthread_self() == this->thread->native_handle()) ? this->pipew.writer() : this->piper.writer();
}
