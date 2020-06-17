#include "UFLRATheory.h"

bool UFLRATheory::simplify(const vec<PFRef>& formulas, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    // Take care of UF simplifications as well
    if (this->keepPartitions()) {
        currentFrame.root = getLogic().mkAnd(currentFrame.formulas);
        lralogic.simplifyAndSplitEq(currentFrame.root, currentFrame.root);
    } else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        auto subs_res = computeSubstitutions(coll_f);
        getTSolverHandler().setSubstitutions(subs_res.usedSubstitution);
        lralogic.simplifyAndSplitEq(subs_res.result, currentFrame.root);
    }
    return true;
}
