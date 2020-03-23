//
// Created by Martin Blicha on 12.12.19.
//

#ifndef OPENSMT_STPSOLVER_H
#define OPENSMT_STPSOLVER_H

#include "TSolver.h"
#include "LALogic.h"
#include "SMTConfig.h"
#include "Graph.hpp"


class STPSolver : TSolver {

    LALogic& logic;

    Graph graph;

    std::vector<Graph> backtracks;

    opensmt::Number parseEdge(PTRef ineq, Edge &edge);

public:
    STPSolver(SMTConfig & c, LALogic & l, vec<DedElem> & d);

    ~STPSolver() override;

    void clearSolver() override;

    void print(ostream & out) override;

    bool assertLit(PtAsgn asgn, bool b = false) override;

    void pushBacktrackPoint() override;

    void popBacktrackPoint() override;

    void popBacktrackPoints(unsigned int i) override;

    TRes check(bool b) override;

    ValPair getValue(PTRef pt) override;

    void computeModel() override;

    void getConflict(bool b, vec<PtAsgn> & vec) override;

    PtAsgn_reason getDeduction() override;

    void declareAtom(PTRef tr) override;

    Logic & getLogic() override;

    bool isValid(PTRef tr) override;

};


#endif //OPENSMT_STPSOLVER_H
