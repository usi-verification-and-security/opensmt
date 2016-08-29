//
// Created by Matteo on 10/12/15.
//

#include <unistd.h>
#include <fcntl.h>
#include <iostream>
#include <random>
#include "client/SolverProcess.h"
#include "OpenSMTSolver.h"


const char *SolverProcess::solver = "OpenSMT2";

const std::string SolverProcess::solve() {
    SMTConfig config;
    config.setRandomSeed(atoi(this->header["seed"].c_str()));

    OpenSMTInterpret interpret(this->header, this->lemmas, config);

    interpret.interpFile((char *) this->instance.c_str());

    sstat status = interpret.main_solver->getStatus();
    std::map<std::string, std::string> header;

    if (status == s_True)
        return "sat";
    else if (status == s_False)
        return "unsat";
    else return "unknown";
}
