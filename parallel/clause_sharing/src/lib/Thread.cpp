//
// Created by Matteo Marescotti on 02/12/15.
//

#include "Thread.h"


pthread_t Thread::init() {
    std::signal(SIGUSR1, [](int signal) {
        if (pthread_self() != Thread::main_thread)
            throw Thread::StopException();
    });
    return pthread_self();
}

pthread_t Thread::main_thread = Thread::init();

Thread::Thread() :
        thread(NULL),
        piper(Pipe::New()),
        pipew(Pipe::New()) {
    pthread_barrier_init(&this->barrier, NULL, 2);
}

Thread::~Thread() {
    pthread_barrier_destroy(&this->barrier);
    try {
        this->check_started();
    }
    catch (ThreadException ex) {
        return;
    }
    this->stop();
}

void Thread::check_started() {
    if (this->thread == NULL)
        throw ThreadException("Thread not started yet");
}

void Thread::check_stopped() {
    if (this->thread != NULL)
        throw ThreadException("Thread already started");
}

void Thread::thread_wrapper() {
    try {
        pthread_barrier_wait(&this->barrier);
        this->main();
    } catch (Thread::StopException ex) { }
}

void Thread::start() {
    this->mtx.lock();
    try {
        this->check_stopped();
        this->thread = new std::thread(&Thread::thread_wrapper, this);
        pthread_barrier_wait(&this->barrier);
    }
    catch (...) {
        mtx.unlock();
        throw;
    }
    this->mtx.unlock();
}

void Thread::stop() {
    this->check_started();
    pthread_kill(this->thread->native_handle(), SIGUSR1);
    this->join();
}

void Thread::join() {
    try {
        this->check_started();
        this->thread->join();
        this->mtx.lock();
        if (this->thread != NULL) {
            delete this->thread;
            this->thread = NULL;
        }
        this->mtx.unlock();
    }
    catch (ThreadException ex) { }
}

Frame &Thread::reader() {
    this->check_started();
    return (pthread_self() == this->thread->native_handle()) ? this->piper.reader() : this->pipew.reader();
}

Frame &Thread::writer() {
    this->check_started();
    return (pthread_self() == this->thread->native_handle()) ? this->pipew.writer() : this->piper.writer();
}