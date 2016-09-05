//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_PROCESSSOLVER_H
#define CLAUSE_SHARING_PROCESSSOLVER_H

#include <thread>
#include "lib/Process.h"
#include "lib/net/Pipe.h"


enum Status {
    unknown, sat, unsat
};

typedef struct {
    const enum {
        incremental, partition, resume
    } command;
    std::string smtlib;
    uint8_t partitions;
} Task;

class SolverProcess : public Process {
private:
    Socket *server;
    Socket *lemmas;
    Pipe pipe;
    std::string instance;

    void main() {
        this->init();
        this->report();
        // the cast below is just for the ide to suppress visual error
        std::thread t((std::thread) [&] {
            std::map<std::string, std::string> header;
            std::string payload;
            while (true) {
                // receives both commands from the server(forwarded by SolverServer) and from SolverServer.
                // if command=local the answer is built here and delivered to SolverServer
                // otherwise the solver is interrupted and the message forwarder through pipe
                this->reader()->read(header, payload);
                if (header.count("command") == 0)
                    continue;
                if (header["command"] == "local" && header.count("local") == 1) {
                    if (header["local"] == "report")
                        this->report();
                    continue;
                }
                this->interrupt();
                this->pipe.writer()->write(header, payload);
            }
        });
        this->solve();
    }

    // here the module can write class fields
    void init();

    // class field are read only
    void solve();

    // async interrupt the solver
    void interrupt();

    void report() {
        this->writer()->write(this->header, "");
    }

    void report(Status status) {
        auto header = this->header;
        if (status == Status::sat)
            header["status"] = "sat";
        else if (status == Status::unsat)
            header["status"] = "unsat";
        else return;//header["status"] = "unknown";
        this->writer()->write(header, "");

    }

    Task wait() {
        std::map<std::string, std::string> header;
        std::string payload;
        this->pipe.reader()->read(header, payload);
        if (header["command"] == "incremental") {
            return Task{
                    .command=Task::incremental,
                    .smtlib=payload
            };
        }
        return Task{
                .command=Task::resume
        };
    }

public:
    SolverProcess(Socket *lemmas,
                  std::map<std::string, std::string> header,
                  std::string instance) :
            lemmas(lemmas),
            pipe(Pipe()),
            instance(instance),
            header(header) {
        this->start();
    }

    std::map<std::string, std::string> header;

    static const char *solver;
};

#endif //CLAUSE_SHARING_PROCESSSOLVER_H
