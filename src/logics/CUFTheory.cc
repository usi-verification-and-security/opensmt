#include "Theory.h"

const int CUFTheory::i_default_bitwidth = 32;

//
// Simplify with unit propagation, add the diamond equalities if
// present.
//
// This function adds the newly introduced partial interpretations to
// the top frame.
//
bool CUFTheory::simplify(const vec<PFRef>& formulas, int curr)
{

    if (this->keepPartitions()) {
        pfstore[formulas[curr]].root = getLogic().mkAnd(pfstore[formulas[curr]].formulas);
        return true;
    }
    else {
        PTRef coll_f = getCollateFunction(formulas, curr);

        PTRef trans = getLogic().learnEqTransitivity(coll_f);
        pfstore[formulas[curr]].push(trans);

        bool res = computeSubstitutions(coll_f, formulas, curr);
        PTRef substs_formula = getSubstitutionsFormulaFromUnits(pfstore[formulas[curr]].units);
        pfstore[formulas[curr]].substs = substs_formula;
        return res;
    }
}

