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
        pipew(Pipe::New()) { }

Thread::~Thread() {
    try {
        this->check_started();
        this->Stop();
    }
    catch (ThreadException ex) { }
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
        this->mtx_start.unlock();
        this->main();
    } catch (Thread::StopException ex) { }
}

void Thread::Start() {
    static std::mutex mtx;
    mtx.lock();
    try {
        this->check_stopped();
        this->mtx_start.lock();
        this->thread = new std::thread(&Thread::thread_wrapper, this);
        this->mtx_start.lock();
    }
    catch (...) {
        mtx.unlock();
        throw;
    }
    mtx.unlock();
}

void Thread::Stop() {
    this->check_started();
    pthread_kill(this->thread->native_handle(), SIGUSR1);
    this->Join();
}

void Thread::Join() {
    static std::mutex mtx;
    try {
        this->check_started();
        this->thread->join();
        mtx.lock();
        if (this->thread != NULL) {
            delete this->thread;
            this->thread = NULL;
            this->mtx_start.unlock();
        }
        mtx.unlock();
    }
    catch (ThreadException ex) { }
}

Frame &Thread::Reader() {
    this->check_started();
    return (pthread_self() == this->thread->native_handle()) ? this->piper.Reader() : this->pipew.Reader();
}

Frame &Thread::Writer() {
    this->check_started();
    return (pthread_self() == this->thread->native_handle()) ? this->pipew.Writer() : this->piper.Writer();
}