#include "Theory.h"

bool LRATheory::simplify(vec<PushFrame>& formulas, int curr)
{
    PTRef coll_f = getCollateFunction(formulas, curr);
    bool res = computeSubstitutions(coll_f, formulas, curr);
    lralogic.simplifyAndSplitEq(formulas[curr].root, formulas[curr].root);
    return true;
}


