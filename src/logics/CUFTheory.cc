#include "Theory.h"

const int CUFTheory::i_default_bitwidth = 32;

//
// Simplify with unit propagation, add the diamond equalities if
// present.
//
// This function adds the newly introduced partial interpretations to
// the top frame.
//
bool CUFTheory::simplify(const vec<PFRef>& formulas, PartitionManager& pmanager, int curr)
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
        setSubstitutions(std::move(subs_res.usedSubstitution));
    }
    return true;
}

