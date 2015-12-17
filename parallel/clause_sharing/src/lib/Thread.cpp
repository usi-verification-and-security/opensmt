//
// Created by Matteo Marescotti on 02/12/15.
//

#include "Thread.h"


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
