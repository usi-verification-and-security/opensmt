#include "Theory.h"

bool UFTheory::simplify(vec<PushFrame>& formulas, int curr)
{

    PTRef coll_f = getCollateFunction(formulas, curr);

    PTRef trans = getLogic().learnEqTransitivity(coll_f);
    formulas[curr].push(trans);

    bool res = computeSubstitutions(coll_f, formulas, curr);
    return res;
}

