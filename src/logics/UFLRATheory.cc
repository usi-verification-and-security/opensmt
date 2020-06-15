#include "UFLRATheory.h"

bool UFLRATheory::simplify(const vec<PFRef>& formulas, int curr)
{
    // Take care of UF simplifications as well
    if (this->keepPartitions()) {
        pfstore[formulas[curr]].root = getLogic().mkAnd(pfstore[formulas[curr]].formulas);
    } else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        computeSubstitutions(coll_f, formulas, curr);
    }
    lralogic.simplifyAndSplitEq(pfstore[formulas[curr]].root, pfstore[formulas[curr]].root);
    return true;
}
