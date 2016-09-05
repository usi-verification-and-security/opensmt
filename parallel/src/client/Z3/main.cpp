//
// Created by Matteo on 29/08/16.
//

#include "z3++.h"
#include <istream>
#include <fstream>


int main(int argc, char **argv) {
    std::string payload;
    std::ifstream file(argv[1]);
    file.seekg(0, std::ios::end);
    payload.resize((unsigned long) file.tellg());
    file.seekg(0, std::ios::beg);
    file.read(&payload[0], payload.size());
    file.close();

    z3::context context;
    Z3_ast a = Z3_parse_smtlib2_string(context, payload.c_str(), 0, 0, 0, 0, 0, 0);
    z3::expr e(context, a);
    z3::solver solver(context);
    solver.add(e);
    z3::check_result status = solver.check();
    return 0;
}