#include "Theory.h"

//
// Unit propagate with simplifications and split equalities into
// inequalities.  If PRODUCE_PROOF is enabled, only do the splitting to
// inequalities.
//
bool LIATheory::simplify(const vec<PFRef>& formulas, int curr)
{
#ifdef PRODUCE_PROOF
    vec<PTRef> & flas = pfstore[formulas[curr]].formulas;
    for(int i = 0; i <flas.size(); ++i) {
        PTRef & fla = flas[i];
        lialogic.simplifyAndSplitEq(fla, fla);
    }
    pfstore[formulas[curr]].root = getLogic().mkAnd(flas);
#else // PRODUCE_PROOF
    PTRef coll_f = getCollateFunction(formulas, curr);
    bool res = computeSubstitutions(coll_f, formulas, curr);
    lialogic.simplifyAndSplitEq(pfstore[formulas[curr]].root, pfstore[formulas[curr]].root);
    vec<Map<PTRef,lbool,PTRefHash>::Pair> units;
    pfstore[formulas[curr]].units.getKeysAndVals(units);
    vec<PTRef> substs_vec;
    for (int i = 0; i < units.size(); i++) {
        if (units[i].data == l_True) {
            substs_vec.push(units[i].key);
        }
    }
    PTRef substs_formula = lialogic.mkAnd(substs_vec);
    lialogic.simplifyAndSplitEq(substs_formula, pfstore[formulas[curr]].substs);
#endif // PRODUCE_PROOF
    return true;
}
