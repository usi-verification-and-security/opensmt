//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_PROCESSSOLVER_H
#define CLAUSE_SHARING_PROCESSSOLVER_H

#include "Settings.h"
#include "lib/Process.h"
#include "SimpSMTSolver.h"


namespace opensmt {
    extern bool stop;
}


class _SMTSolver : public SimpSMTSolver {
private:
    std::string name;
    std::string hash;

    void inline clausesPublish() { }

    void inline clausesUpdate() { }

public:
    _SMTSolver(Settings &, std::string, std::string, SMTConfig &, THandler &);

    ~_SMTSolver();

};


class ProcessSolver : public Process {
private:
    Settings &settings;
    std::string name;
    std::string hash;
    std::string instance;

protected:
    void main();

public:
    ProcessSolver(Settings &, std::string, std::string, std::string);

};

#endif //CLAUSE_SHARING_PROCESSSOLVER_H
