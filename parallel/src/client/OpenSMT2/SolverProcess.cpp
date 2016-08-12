//
// Created by Matteo on 10/12/15.
//

#include <unistd.h>
#include <fcntl.h>
#include <iostream>
#include "Interpret.h"
#include "lib/Log.h"
#include "client/SolverProcess.h"
#include "OpenSMTSolver.h"


const char *SolverProcess::solver = "OpenSMT2";

SolverProcess::SolverProcess(Socket *lemmas, std::map<std::string, std::string> header, std::string instance) :
        Process(),
        lemmas(lemmas),
        header(header),
        instance(instance) {
    if (this->header.count("seed") == 0) {
        std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
        std::random_device rd;
        this->header["seed"] = std::to_string(randuint(rd));
    }
    this->start();
}

void SolverProcess::main() {

    if (this->header.count("stderr") == 0)
        this->header["stderr"] = "/dev/null";
    if (this->header["stderr"] != "-") {
        FILE *file = fopen(this->header["stderr"].c_str(), "a+");
        dup2(fileno(file), fileno(stderr));
        fclose(file);
    }

    if (this->header.count("stdout") == 0)
        this->header["stdout"] = "/dev/null";
    if (this->header["stdout"] != "-") {
        FILE *file = fopen(this->header["stdout"].c_str(), "a+");
        dup2(fileno(file), fileno(stdout));
        fclose(file);
    }

    SMTConfig config;
    config.setRandomSeed(atoi(this->header["seed"].c_str()));

    OpenSMTInterpret interpret(this->header, this->lemmas, config);

    interpret.interpFile((char *) this->instance.c_str());

    sstat status = interpret.main_solver->getStatus();
    std::map<std::string, std::string> header;
    std::string payload;

    if (status == s_True)
        header["status"] = "sat";
    else if (status == s_False)
        header["status"] = "unsat";
    else header["status"] = "unknown";

    header["name"] = this->header["name"];
    header["node"] = this->header["node"];

    this->writer()->write(header, payload);

}