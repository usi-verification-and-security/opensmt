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


const char *SolverProcess::solver = "Z3";

const std::string SolverProcess::solve() {
    z3::context ctx;
    Z3_ast a = Z3_parse_smtlib2_string(ctx, this->instance.c_str(), 0, 0, 0, 0, 0, 0);
    z3::expr e(ctx, a);
    z3::solver s(ctx);
    s.add(e);
    z3::check_result status = s.check();
    if (status == z3::check_result::sat)
        return "sat";
    else if (status == z3::check_result::unsat)
        return "unsat";
    else return "unknown";
}
