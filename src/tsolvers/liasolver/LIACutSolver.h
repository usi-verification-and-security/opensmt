//
// Created by prova on 28.08.18.
//

#ifndef OPENSMT_LIACUTSOLVER_H
#define OPENSMT_LIACUTSOLVER_H

#include "LIASolver.h"
#include "Matrix.h"
#include "lasolver/Tableau.h"



class LIACutSolver : public LIASolver {
private:
    LAVecAllocator va;
    LAVecStore vecStore;
    LAMatrixStore ms;
    Map<LVRef,int,LVRefHash> vars;
    vec<LVRef> colToVar;


    void pivotOnSmallestConsistentInPoly(LVRef var, Simplex& s);

public:
    LIACutSolver(SMTConfig& c, LIALogic& l, vec<DedElem>& d)
            : LIASolver(c, l, d)
            , vecStore(va, l)
            , ms(vecStore)
    {}

    TRes check    (bool complete) override;
    bool explicitEqualityCheck();
    TRes checkIntegersAndSplit(Simplex& s, LRAModel& m);
    void fixEqualities(LVRef basicVar, Simplex& s, LRAModel& m);
    void initialize(Simplex& s, LRAModel& m);
    std::unique_ptr<Simplex> computeEqualityBasis();
};


#endif //OPENSMT_LIACUTSOLVER_H
