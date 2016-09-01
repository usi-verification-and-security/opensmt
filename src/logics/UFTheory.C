#include "Theory.h"
//
// Simplify with unit propagation, add the diamond equalities if
// present.  If PRODUCE_PROOF is enabled, do no simplifications but just
// update the root.
//
bool UFTheory::simplify(vec<PushFrame>& formulas, int curr)
{
#ifdef PRODUCE_PROOF
    formulas[curr].root = getLogic().mkAnd(formulas[curr].formulas);
    return true;
#endif
    PTRef coll_f = getCollateFunction(formulas, curr);

    PTRef trans = getLogic().learnEqTransitivity(coll_f);
    formulas[curr].push(trans);

    bool res = computeSubstitutions(coll_f, formulas, curr);
    return res;
}

