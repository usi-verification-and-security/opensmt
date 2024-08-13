//
// Created by Martin Blicha on 12.12.19.
//

#ifndef OPENSMT_STPSOLVER_H
#define OPENSMT_STPSOLVER_H

#include "STPGraphManager.h"
#include "STPMapper.h"
#include "STPModel.h"
#include "SafeInt.h"

#include <logics/ArithLogic.h>
#include <options/SMTConfig.h>
#include <tsolvers/TSolver.h>
// implementations of template functions #included below class definition

#include <memory>

namespace opensmt {
template<typename T>
class STPSolver : public TSolver {
public:
    STPSolver(SMTConfig & c, ArithLogic & l);

    void clearSolver() override;

    bool assertLit(PtAsgn asgn) override;

    void pushBacktrackPoint() override;

    void popBacktrackPoint() override;

    void popBacktrackPoints(unsigned int i) override;

    TRes check(bool b) override;

    void fillTheoryFunctions(ModelBuilder & modelBuilder) const override;

    void computeModel() override;

    void getConflict(vec<PtAsgn> &) override;

    void declareAtom(PTRef tr) override;

    Logic & getLogic() override;

    bool isValid(PTRef tr) override;

private:
    struct ParsedPTRef {
        // represents inequalities of the form 'y - x <= c'
        // this corresponds to edges 'y --c--> x'
        PTRef x; // destination of the edge
        PTRef y; // source of the edge
        T c;     // cost of the edge
    };

    ParsedPTRef parseRef(PTRef ref) const;

    ArithLogic & logic;

    STPStore<T> store;

    STPMapper<T> mapper;

    STPGraphManager<T> graphMgr;

    size_t inv_bpoint; // backtrack point where we entered an inconsistent state
    PtAsgn inv_asgn;

    std::unique_ptr<STPModel<T>> model; // mapping of vertices (vars) to valid assignments, if it was computed
};
} // namespace opensmt

#include "STPSolver_implementations.hpp"

#endif // OPENSMT_STPSOLVER_H
