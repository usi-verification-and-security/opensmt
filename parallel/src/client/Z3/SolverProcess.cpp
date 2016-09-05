//
// Created by Matteo on 10/12/15.
//

#include <unistd.h>
#include <fcntl.h>
#include <random>
#include <iostream>
#include "lib/Log.h"
#include "client/SolverProcess.h"
#include "z3++.h"
#include "/usr/local/include/z3++.h"


z3::context *context = nullptr;
z3::solver *solver = nullptr;

const char *SolverProcess::solver = "Z3";

void SolverProcess::init() { }

void SolverProcess::solve() {
    context = new z3::context;
    Z3_ast a = Z3_parse_smtlib2_string(*context, this->instance.c_str(), 0, 0, 0, 0, 0, 0);
    z3::expr e(*context, a);
    ::solver = new z3::solver(*context);
    ::solver->add(e);
    z3::check_result status = ::solver->check();
    if (status == z3::check_result::sat)
        this->report(Status::sat);
    else if (status == z3::check_result::unsat)
        this->report(Status::unsat);
    else this->report(Status::unknown);
}

void SolverProcess::interrupt() {
    context->interrupt();
}