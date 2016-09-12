#include "Theory.h"

//
// Unit propagate with simplifications and split equalities into
// inequalities.  If PRODUCE_PROOF is enabled, only do the splitting to
// inequalities.
//
bool LRATheory::simplify(vec<PFRef>& formulas, int curr)
{
#ifndef PRODUCE_PROOF
    PTRef coll_f = getCollateFunction(formulas, curr);
    bool res = computeSubstitutions(coll_f, formulas, curr);
#else
    pfstore[formulas[curr]].root = getLogic().mkAnd(pfstore[formulas[curr]].formulas);
#endif
    lralogic.simplifyAndSplitEq(pfstore[formulas[curr]].root, pfstore[formulas[curr]].root);
    return true;
}


