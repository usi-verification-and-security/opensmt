#include "Theory.h"

bool RDLTheory::simplify(const vec<PFRef> &formulas, PartitionManager&, int curr) {
    PTRef coll_f = getCollateFunction(formulas, curr);
    auto subs_res = computeSubstitutions(coll_f);
    PTRef finalFla = flaFromSubstitutionResult(subs_res);
    getTSolverHandler().setSubstitutions(subs_res.usedSubstitution);
    auto & currentFrame = pfstore[formulas[curr]];
    lralogic.simplifyAndSplitEq(finalFla, currentFrame.root);
    return true;
}