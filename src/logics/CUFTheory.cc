#include "Theory.h"

const int CUFTheory::i_default_bitwidth = 32;

//
// Simplify with unit propagation, add the diamond equalities if
// present.  If PRODUCE_PROOF is enabled, do no simplifications but just
// update the root.
//
// This function adds the newly introduced partial interpretations to
// the top frame.
//
bool CUFTheory::simplify(const vec<PFRef>& formulas, int curr)
{

#ifdef PRODUCE_PROOF
    pfstore[formulas[curr]].root = getLogic().mkAnd(pfstore[formulas[curr]].formulas);
    return true;
#endif

    PTRef coll_f = getCollateFunction(formulas, curr);

    PTRef trans = getLogic().learnEqTransitivity(coll_f);
    pfstore[formulas[curr]].push(trans);

    bool res = computeSubstitutions(coll_f, formulas, curr);
    vec<Map<PTRef,lbool,PTRefHash>::Pair> units;
    pfstore[formulas[curr]].units.getKeysAndVals(units);
    vec<PTRef> substs_vec;
    for (int i = 0; i < units.size(); i++) {
        if (units[i].data == l_True) {
            substs_vec.push(units[i].key);
        }
    }
    PTRef substs_formula = cuflogic.mkAnd(substs_vec);
    pfstore[formulas[curr]].substs = substs_formula;
    return res;
}

