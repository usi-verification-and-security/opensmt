#include "Theory.h"
//
// Simplify with unit propagation, add the diamond equalities if
// present.  If PRODUCE_PROOF is enabled, do no simplifications but just
// update the root.  So far this is the same as UFTheory's simplify.
//
bool CUFTheory::simplify(vec<PFRef>& formulas, int curr)
{
#ifdef PRODUCE_PROOF
    pfstore[formulas[curr]].root = getLogic().mkAnd(pfstore[formulas[curr]].formulas);
    return true;
#endif
    PTRef coll_f = getCollateFunction(formulas, curr);

    PTRef trans = getLogic().learnEqTransitivity(coll_f);
    pfstore[formulas[curr]].push(trans);

    bool res = computeSubstitutions(coll_f, formulas, curr);
    return res;
}

