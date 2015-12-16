//
// Created by Matteo Marescotti on 02/12/15.
//

#include "Process.h"


Process::Process() :
        process(0), piper(Pipe::New()), pipew(Pipe::New()) { }

Process::~Process() {
    this->stop();
    this->join();
}

void Process::start() {
    this->process = fork();
    if (this->process < 0)
        throw ProcessException("fork error");
    if (this->process == 0) {
        this->piper.writer().close();
        this->pipew.reader().close();
        this->main();
        exit(0);
    }
    else {
        this->piper.reader().close();
        this->pipew.writer().close();
    }
}

void Process::stop() {
    if (this->process > 0)
        kill(this->process, SIGINT);
}

void Process::join() {
    if (this->process > 0)
        waitpid(this->process, NULL, 0);
}

Frame &Process::reader() {
    return (this->process == 0) ? this->piper.reader() : this->pipew.reader();
}

Frame &Process::writer() {
    return (this->process == 0) ? this->pipew.writer() : this->piper.writer();
}
