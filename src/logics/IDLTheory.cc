//
// Created by Martin Blicha on 10.05.20.
//

#include "Theory.h"

//
// Unit propagate with simplifications and split equalities into
// inequalities.
//
bool IDLTheory::simplify(const vec<PFRef>& formulas, PartitionManager&, int curr)
{
    PTRef coll_f = getCollateFunction(formulas, curr);
    auto subs_res = computeSubstitutions(coll_f);
    PTRef finalFla = flaFromSubstitutionResult(subs_res);
    getTSolverHandler().setSubstitutions(subs_res.usedSubstitution);
    auto & currentFrame = pfstore[formulas[curr]];
    lialogic.simplifyAndSplitEq(finalFla, currentFrame.root);
    return true;
}

