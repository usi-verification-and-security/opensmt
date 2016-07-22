//
// Created by Matteo on 22/07/16.
//

#ifndef CLAUSE_SERVER_OPENSMTSOLVER_H
#define CLAUSE_SERVER_OPENSMTSOLVER_H

#include "SimpSMTSolver.h"
#include "client/Settings.h"


namespace opensmt {
    extern bool stop;
}


class OpenSMTSolver : public SimpSMTSolver {
private:
    void inline clausesPublish() { }

    void inline clausesUpdate() { }

    std::string name;
    std::string hash;
public:
    OpenSMTSolver(Settings &, std::string, std::string, SMTConfig &, THandler &);

    ~OpenSMTSolver();

};


#endif //CLAUSE_SERVER_OPENSMTSOLVER_H
