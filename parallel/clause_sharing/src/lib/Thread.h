//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_THREAD_H
#define CLAUSE_SHARING_THREAD_H

#include <thread>
#include <mutex>
#include <atomic>
#include <csignal>
#include <iostream>
#include "Exception.h"
#include "Frame.h"


//class ThreadException : public Exception {
//public:
//    explicit ThreadException(const char *message) : Exception(message) { }
//
//    explicit ThreadException(const std::string &message) : Exception(message) { }
//};


class Thread {
private:
    static pthread_t main_thread;

    static pthread_t init();

    std::thread *thread;
    pthread_barrier_t barrier;
    Pipe piper;
    Pipe pipew;
    std::mutex mtx;
    std::atomic<bool> stop_requested;

    void thread_wrapper();

protected:
    virtual void main() = 0;

    void start();

    class StopException : public std::exception {
    public:
        char const *what() const throw() { return "Thread is requested to stop."; }
    };

public:
    Thread();

    virtual ~Thread();

    void stop();

    void join();

    bool joinable();

    Frame &reader();

    Frame &writer();

};


#endif //CLAUSE_SHARING_THREAD_H
