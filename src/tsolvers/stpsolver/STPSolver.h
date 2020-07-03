//
// Created by Martin Blicha on 12.12.19.
//

#ifndef OPENSMT_STPSOLVER_H
#define OPENSMT_STPSOLVER_H

#include <memory>
#include "TSolver.h"
#include "LALogic.h"
#include "SMTConfig.h"
#include "STPMapper.h"
#include "STPEdgeGraph.h"
#include "STPModel.h"

struct ParsedPTRef {
    // represents inequalities of the form 'y <= x + c'
    // this corresponds to edges 'y --c--> x'
    PTRef x;            // destination of the edge
    PTRef y;            // source of the edge
    ptrdiff_t c;  // cost of the edge
};

class STPSolver : public TSolver {

    LALogic& logic;

    STPStore store;

    STPMapper mapper;

    STPGraphManager graphMgr;

    ptrdiff_t inv_bpoint;                      // backtrack point where we entered an inconsistent state
    PtAsgn inv_asgn;

    std::unique_ptr<STPModel> model;           // mapping of vertices (vars) to valid assignments, if it was computed

    ParsedPTRef parseRef(PTRef ref) const;

    // Given an edge, add the negation of that edge to 'store' and mark them as negations
    EdgeRef createNegation(EdgeRef e);

public:
    STPSolver(SMTConfig & c, LALogic & l);

    ~STPSolver() override;

    void clearSolver() override;

    void print(ostream & out) override;

    bool assertLit(PtAsgn asgn) override;

    void pushBacktrackPoint() override;

    void popBacktrackPoint() override;

    void popBacktrackPoints(unsigned int i) override;

    TRes check(bool b) override;

    ValPair getValue(PTRef pt) override;

    void computeModel() override;

    void getConflict(bool b, vec<PtAsgn> & vec) override;

    void declareAtom(PTRef tr) override;

    Logic & getLogic() override;

    bool isValid(PTRef tr) override;

};


#endif //OPENSMT_STPSOLVER_H
