//
// Created by Matteo on 10/12/15.
//

#include "main.h"


namespace opensmt {
    extern bool stop;
}


void _SMTSolver::clausesPublish() { }

void _SMTSolver::clausesUpdate() { }


ThreadSolver::ThreadSolver(std::string &channel, std::string &osmt2) :
        Thread(), channel(channel), osmt2(osmt2), status(s_Undef), msg(NULL) {
    this->start();
}

ThreadSolver::~ThreadSolver() {
    free(this->msg);
}

void ThreadSolver::main() {
    try {
        this->solve();
        this->stop();
    }
    catch (...) { }
    char s = this->status.getValue();
    this->writer().write(&s, 1);
}

void ThreadSolver::solve() {

//    std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
//    std::random_device rd;
//    SMTConfig config;
//    config.setRandomSeed(randuint(rd));
//
//    Theory *theory = new LRATheory(config);
//
//    _Solver *solver = new _Solver(this->channel, *theory, config);
//    solver->initialize();
//
//    if (solver->readSolverState((int *) this->osmt2.c_str(), (int) this->osmt2.size(), true, &this->msg)) {
//        this->status = solver->simplifyFormulas(&this->msg);
//        if (this->status != s_True && this->status != s_False)
//            this->status = solver->solve();
//    }
}
