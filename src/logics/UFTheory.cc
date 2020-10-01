#include "Theory.h"
//
// Simplify with unit propagation, add the diamond equalities if
// present.  If partitions cannot mix, do no simplifications but just
// update the root.
//
bool UFTheory::simplify(const vec<PFRef>& formulas, PartitionManager &pmanager, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    if (this->keepPartitions()) {
        currentFrame.root = getLogic().mkAnd(currentFrame.formulas);
    }
    else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        PTRef trans = getLogic().learnEqTransitivity(coll_f);
        coll_f = getLogic().mkAnd(coll_f, trans);
        auto subs_res = computeSubstitutions(coll_f);
        currentFrame.root = flaFromSubstitutionResult(subs_res);
        getTSolverHandler().setSubstitutions(subs_res.usedSubstitution);
    }
    return true;
}

