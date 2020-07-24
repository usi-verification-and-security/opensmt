//
// Created by Martin Blicha on 10.05.20.
//

#include "Theory.h"

//
// Unit propagate with simplifications and split equalities into
// inequalities.
//
bool IDLTheory::simplify(const vec<PFRef>& formulas, int curr)
{
    PTRef coll_f = getCollateFunction(formulas, curr);
    computeSubstitutions(coll_f, formulas, curr);
    lialogic.simplifyAndSplitEq(pfstore[formulas[curr]].root, pfstore[formulas[curr]].root);
    PTRef substs_formula = getSubstitutionsFormulaFromUnits(pfstore[formulas[curr]].units);
    lialogic.simplifyAndSplitEq(substs_formula, pfstore[formulas[curr]].substs);
    return true;
}

