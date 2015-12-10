//
// Created by Matteo on 10/12/15.
//

#include "main.h"


namespace opensmt {
    extern bool stop;
}


void _SMTSolver::clausesPublish() { }

void _SMTSolver::clausesUpdate() { }


ThreadSolver::~ThreadSolver() {
    if (this->msg != NULL)
        free(this->msg);
}

void ThreadSolver::main() {

    char s = s_Undef.getValue();
    this->writer().write(&s, 1);
    return;

    std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
    std::random_device rd;
    SMTConfig config;
    config.setRandomSeed(randuint(rd));

    Theory *theory = new LRATheory(config);

    _Solver *solver = new _Solver(this->channel, *theory, config);
    solver->initialize();

    if (!solver->readSolverState((int *) this->osmt2.c_str(), (int) this->osmt2.size(), true, &this->msg))
        return;
    //std::cout << "Started job " << jid << "\n";
    this->status = solver->simplifyFormulas(&this->msg);
    if (this->status != s_True && this->status != s_False)
        this->status = solver->solve();
}
