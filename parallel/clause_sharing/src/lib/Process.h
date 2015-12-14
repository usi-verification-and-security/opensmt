//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_PROCESS_H
#define CLAUSE_SHARING_PROCESS_H

#include <thread>
#include <mutex>
#include <atomic>
#include <csignal>
#include <iostream>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/wait.h>
#include "Exception.h"
#include "Frame.h"


class ProcessException : public Exception {
public:
    explicit ProcessException(const char *message) : Exception(message) { }

    explicit ProcessException(const std::string &message) : Exception(message) { }
};


class Process {
private:
    void process_wrapper();

    pid_t process;
    Pipe piper;
    Pipe pipew;

protected:
    virtual void main() = 0;

    void start();

    class StopException : public std::exception {
    public:
        char const *what() const throw() { return "Process is requested to stop."; }
    };

public:
    Process();

    virtual ~Process();

    void stop();

    void join();

    Frame &reader();

    Frame &writer();

};


#endif //CLAUSE_SHARING_PROCESS_H
