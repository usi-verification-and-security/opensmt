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
#include "SafeInt.hpp"

template<typename T> class STPSolver : public TSolver {
private:
    struct ParsedPTRef {
        // represents inequalities of the form 'y - x <= c'
        // this corresponds to edges 'y --c--> x'
        PTRef x;            // destination of the edge
        PTRef y;            // source of the edge
        T c;                // cost of the edge
    };

    LALogic& logic;

    STPStore<T> store;

    STPMapper<T> mapper;

    STPGraphManager<T> graphMgr;

    size_t inv_bpoint;                      // backtrack point where we entered an inconsistent state
    PtAsgn inv_asgn;

    std::unique_ptr<STPModel<T>> model;           // mapping of vertices (vars) to valid assignments, if it was computed

    ParsedPTRef parseRef(PTRef ref) const;

    static T convert(const opensmt::Number &cost);

    static T negate(const T &cost);

    static std::string show(const T &val);

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
