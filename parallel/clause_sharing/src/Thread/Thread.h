//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_THREAD_H
#define CLAUSE_SHARING_THREAD_H

#include <thread>
#include <csignal>
#include <exception>


class Thread {

private:
    std::thread *thread;

    void thread_wrapper();

protected:
    virtual void thread_main() = 0;

    class StopException : public std::exception {
    public:
        char const *what() const throw() { return "Thread is requested to stop."; }
    };

public:
    Thread();

    virtual ~Thread();

    void Start();

    void Stop();

};


#endif //CLAUSE_SHARING_THREAD_H
