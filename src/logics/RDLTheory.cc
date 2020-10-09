#include "Theory.h"

bool RDLTheory::simplify(const vec<PFRef> &formulas, int curr)
{
    PTRef coll_f = getCollateFunction(formulas, curr);
    computeSubstitutions(coll_f, formulas, curr);
    lralogic.simplifyAndSplitEq(pfstore[formulas[curr]].root, pfstore[formulas[curr]].root);
    PTRef substs_formula = getSubstitutionsFormulaFromUnits(pfstore[formulas[curr]].units);
    lralogic.simplifyAndSplitEq(substs_formula, pfstore[formulas[curr]].substs);
    return true;
}