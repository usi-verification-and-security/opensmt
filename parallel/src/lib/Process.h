//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_PROCESS_H
#define CLAUSE_SHARING_PROCESS_H

#include "Exception.h"
#include "net.h"


class ProcessException : public Exception {
public:
    explicit ProcessException(const char *message) : ProcessException(std::string(message)) { }

    explicit ProcessException(const std::string &message) : Exception("ProcessException: " + message) { }
};


class Process {
private:
    pid_t process;
    Pipe piper;
    Pipe pipew;

protected:
    virtual void main() = 0;

    void start();

public:
    Process();

    virtual ~Process();

    void stop();

    void join();

    inline bool joinable();

    Socket *reader();

    Socket *writer();

};


#endif //CLAUSE_SHARING_PROCESS_H
