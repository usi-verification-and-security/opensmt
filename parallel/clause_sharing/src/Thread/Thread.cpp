//
// Created by Matteo Marescotti on 02/12/15.
//

#include "Thread.h"


Thread::Thread() {
    this->thread = NULL;
}

Thread::~Thread() {
    if (this->thread != NULL)
        this->Stop();
}

void Thread::Start() {
    if (this->thread == NULL)
        this->thread = new std::thread(&Thread::thread_wrapper, this);
    else
        throw "already started";
}

void Thread::Stop() {
    pthread_kill(this->thread->native_handle(), SIGINT);
    this->thread->join();
    delete this->thread;
    this->thread = NULL;
}

void Thread::thread_wrapper() {
    std::signal(SIGINT, [](int signal) {
        throw Thread::StopException();
    });

    this->thread_main();
}
