#include "Theory.h"
//
// Simplify with unit propagation, add the diamond equalities if
// present.  If partitions cannot mix, do no simplifications but just
// update the root.
//
bool UFTheory::simplify(const vec<PFRef>& formulas, int curr)
{
    if (this->keepPartitions()) {
        pfstore[formulas[curr]].root = getLogic().mkAnd(pfstore[formulas[curr]].formulas);
        return true;
    }
    else {
        PTRef coll_f = getCollateFunction(formulas, curr);

        PTRef trans = getLogic().learnEqTransitivity(coll_f);
        coll_f = getLogic().isTrue(trans) ? coll_f : getLogic().mkAnd(coll_f, trans);

        bool res = computeSubstitutions(coll_f, formulas, curr);
        return res;
    }
}

