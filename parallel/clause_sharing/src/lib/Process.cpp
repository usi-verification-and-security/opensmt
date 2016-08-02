//
// Created by Matteo Marescotti on 02/12/15.
//

#include "Process.h"
#include <csignal>
#include <unistd.h>


Process::Process() :
        process(-1), piper(Pipe()), pipew(Pipe()) { }

Process::~Process() {
    this->stop();
    this->join();
}

void Process::start() {
    this->process = ::fork();
    if (this->process < 0)
        throw ProcessException("fork error");
    if (this->process == 0) {
        this->piper.writer()->close();
        this->pipew.reader()->close();
        this->main();
        exit(0);
    }
    else {
        this->piper.reader()->close();
        this->pipew.writer()->close();
    }
}

void Process::stop() {
    if (this->joinable()) {
        kill(this->process, SIGINT);
        this->join();
    }
}

void Process::join() {
    if (this->joinable()) {
        waitpid(this->process, NULL, 0);
        this->process = -1;
    }
}

bool Process::joinable() {
    return this->process > 0;
}

Socket *Process::reader() {
    return (this->process == 0) ? this->piper.reader() : this->pipew.reader();
}

Socket *Process::writer() {
    return (this->process == 0) ? this->pipew.writer() : this->piper.writer();
}
