//
// Created by Matteo Marescotti on 02/12/15.
//

#include "Thread.h"


pthread_t Thread::b() {
    std::signal(SIGUSR1, [](int signal) {
        throw Thread::StopException();
    });
    return pthread_self();
}

pthread_t Thread::main_thread = Thread::b();

Thread::Thread() :
        thread(NULL),
        piper(Frame::Pipe()),
        pipew(Frame::Pipe()) { }

Thread::~Thread() {
    if (this->thread != NULL)
        this->Stop();
}

void Thread::thread_wrapper() {
    std::cout << pthread_self() << "\n";
    try {
        this->mtx_start.unlock();
        this->main();
    } catch (Thread::StopException e) { }
}

void Thread::Start() {
    if (this->thread != NULL)
        throw "Thread already started";
    this->mtx_start.lock();
    this->thread = new std::thread(&Thread::thread_wrapper, this);
    this->mtx_start.lock();
}

void Thread::Stop() {
    if (this->thread == NULL)
        throw "Thread not started yet";
    pthread_kill(this->thread->native_handle(), SIGUSR1);
    this->Join();
    delete this->thread;
    this->thread = NULL;
    this->mtx_start.unlock();
}

void Thread::Join() {
    if (this->thread != NULL)
        this->thread->join();
}

Frame &Thread::Reader() {
    if (this->thread == NULL)
        throw "Thread not started yet";
    return (pthread_self() == this->thread->native_handle()) ? std::get<0>(this->piper) : std::get<0>(this->pipew);
}

Frame &Thread::Writer() {
    if (this->thread == NULL)
        throw "Thread not started yet";
    return (pthread_self() == this->thread->native_handle()) ? std::get<1>(this->pipew) : std::get<1>(this->piper);
}