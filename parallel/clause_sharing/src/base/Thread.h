//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_THREAD_H
#define CLAUSE_SHARING_THREAD_H

#include <thread>
#include <mutex>
#include <csignal>
#include <exception>
#include <iostream>
#include <tuple>
#include "Frame.h"


class Thread {

private:

    static pthread_t main_thread;

    static pthread_t b();

    std::thread *thread;
    std::tuple<Frame, Frame> piper;
    std::tuple<Frame, Frame> pipew;
    std::mutex mtx_start;

    void thread_wrapper();

protected:
    virtual void main() = 0;

    class StopException : public std::exception {
    public:
        char const *what() const throw() { return "Thread is requested to stop."; }
    };

public:
    Thread();

    virtual ~Thread();

    void Start();

    void Stop();

    void Join();

    Frame &Reader();

    Frame &Writer();

};


#endif //CLAUSE_SHARING_THREAD_H
