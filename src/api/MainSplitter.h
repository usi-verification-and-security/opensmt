//
// Created by prova on 01.04.21.
//

#ifndef OPENSMT_MAINSPLITTER_H
#define OPENSMT_MAINSPLITTER_H

#include "MainSolver.h"
#include "ScatterSplitter.h"

class MainSplitter : public MainSolver {

public:

    std::unique_ptr<ScatterSplitter> scatter_Splitter;

    virtual void new_solver()
    {
        this->scatter_Splitter= std::unique_ptr<ScatterSplitter>(new ScatterSplitter(config, thandler));
    };

    MainSplitter(Logic& logic, SMTConfig& config, std::string name)
            :
    //scatter_Splitter(createInnerSolver(config, thandler)),
            MainSolver(logic, config, std::move(name)) {}
    bool writeSolverSplits_smtlib2(const char* file, char** msg) const;
};


#endif //OPENSMT_MAINSPLITTER_H
