#include "UFLRATheory.h"

bool UFLRATheory::simplify(const vec<PFRef>& formulas, int curr)
{
    // Take care of UF simplifications as well
#ifndef PRODUCE_PROOF
    PTRef coll_f = getCollateFunction(formulas, curr);
    bool res = computeSubstitutions(coll_f, formulas, curr);
#else
    pfstore[formulas[curr]].root = getLogic().mkAnd(pfstore[formulas[curr]].formulas);
#endif
    lralogic.simplifyAndSplitEq(pfstore[formulas[curr]].root, pfstore[formulas[curr]].root);
    return true;
}
