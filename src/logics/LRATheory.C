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
    vec<Map<PTRef,lbool,PTRefHash>::Pair> units;
    pfstore[formulas[curr]].units.getKeysAndVals(units);
    vec<PTRef> substs_vec;
    for (int i = 0; i < units.size(); i++) {
        if (units[i].data == l_True) {
            substs_vec.push(units[i].key);
        }
    }
    PTRef substs_formula = lralogic.mkAnd(substs_vec);
    lralogic.simplifyAndSplitEq(substs_formula, pfstore[formulas[curr]].substs);

    return true;
}


