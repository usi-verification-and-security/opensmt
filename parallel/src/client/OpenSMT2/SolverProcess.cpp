//
// Created by Matteo on 10/12/15.
//

#include <unistd.h>
#include <fcntl.h>
#include <iostream>
#include <random>
#include "client/SolverProcess.h"
#include "OpenSMTSolver.h"


using namespace opensmt;

const char *SolverProcess::solver = "OpenSMT2";

void SolverProcess::solve() {
    FILE *file = fopen("/dev/null", "w");
    dup2(fileno(file), fileno(stdout));
    dup2(fileno(file), fileno(stderr));
    fclose(file);

    if (this->header.count("seed") == 0) {
        std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
        std::random_device rd;
        this->header["seed"] = std::to_string(randuint(rd));
    }
    if (this->header.count("lemmas") == 0) {
        this->header["lemmas"] = std::to_string(1000);
    }

    this->report();

    SMTConfig config;
    config.setRandomSeed(atoi(this->header["seed"].c_str()));

    OpenSMTInterpret interpret(this->header, this->lemmas, config);
    interpret.interpFile((char *) this->instance.c_str());
    sstat status = interpret.main_solver->getStatus();

    if (status == s_True)
        this->report(Status::sat);
    else if (status == s_False)
        this->report(Status::unsat);
    else this->report(Status::unknown);
}

void SolverProcess::interrupt() {
    opensmt::stop = true;
}