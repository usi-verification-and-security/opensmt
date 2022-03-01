//
// Created by prova on 01.04.21.
//

#ifndef OPENSMT_MAINSPLITTER_H
#define OPENSMT_MAINSPLITTER_H

#include "MainSolver.h"

class MainSplitter : public MainSolver {
public:
    MainSplitter(Logic& logic, SMTConfig& config, std::string name) : MainSolver(logic, config, std::move(name)) {}
    void writeSolverSplits_smtlib2(std::string const & file) const;
};


#endif //OPENSMT_MAINSPLITTER_H
