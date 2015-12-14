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

void Process::process_wrapper() {
    try {
        this->main();
        return;
    } catch (StopException) { }
}

void Process::start() {
    this->process = fork();
    if (this->process < 0)
        throw ProcessException("fork error");
    if (this->process == 0) {
//        ::close(this->piper.writer().file_descriptor());
//        ::close(this->pipew.reader().file_descriptor());
        this->process_wrapper();
    }
    else {
//        ::close(this->piper.reader().file_descriptor());
//        ::close(this->pipew.writer().file_descriptor());
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
