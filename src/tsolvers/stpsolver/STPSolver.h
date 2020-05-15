//
// Created by Martin Blicha on 12.12.19.
//

#ifndef OPENSMT_STPSOLVER_H
#define OPENSMT_STPSOLVER_H

#include "TSolver.h"
#include "LALogic.h"
#include "SMTConfig.h"
#include "STPMapper.h"
#include "STPEdgeGraph.h"

struct ParsedPTRef {
    // y <= x + c
    PTRef x;            // destination of the edge
    PTRef y;            // source of the edge
    opensmt::Number c;  // cost of the edge
};

class STPSolver : public TSolver {

    LALogic& logic;

    STPStore store;

    STPMapper mapper;

    STPEdgeGraph graph;

    std::vector<uint32_t> backtrack_points;

    size_t curr_bpoint;                 // current backtrack point
    size_t inv_bpoint;                  // backtrack point where we entered an inconsistent state

    ParsedPTRef parseRef(PTRef ref) const;

    EdgeRef createNegation(EdgeRef e);

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
