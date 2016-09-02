//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_PROCESSSOLVER_H
#define CLAUSE_SHARING_PROCESSSOLVER_H

#include <thread>
#include "lib/Process.h"
//#include "SolverThreadd.h"


enum Status {
    unknown, sat, unsat
};

class SolverProcess : public Process {
private:
    Socket *server;
    Socket *lemmas;
    std::map<std::string, std::string> header;
    std::string instance;

    void main() {
        std::thread t([&] {
            std::map<std::string, std::string> header;
            std::string payload;
            while (true) {
                this->reader()->read(header, payload);
                std::cout << payload << "\n";
            }
        });
        this->solve();
    }


    void solve();

    void interrupt();

    void report() {
        this->server->write(this->header, "");
    }

    void report(Status status) {
        auto header = this->header;
        if (status == Status::sat)
            header["status"] = "sat";
        else if (status == Status::unsat)
            header["status"] = "unsat";
        else header["status"] = "unknown";
        this->server->write(header, "");
    }

    void wait() {

    }

public:
    SolverProcess(Socket *server,
                  Socket *lemmas,
                  std::map<std::string, std::string> header,
                  std::string instance) :
            server(server),
            lemmas(lemmas),
            header(header),
            instance(instance) {
        this->start();
    }

    std::map<std::string, std::string> &get_header() { return this->header; }

    static const char *solver;
};

#endif //CLAUSE_SHARING_PROCESSSOLVER_H
