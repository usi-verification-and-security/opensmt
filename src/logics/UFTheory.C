#include "Theory.h"

// (1) Construct the collate function as a conjunction of formulas up to curr.
// (2) From the coll function compute units_{curr}
// (3) Use units_1 /\ ... /\ units_{curr} to simplify formulas[curr]
bool UFTheory::simplify(vec<PushFrame>& formulas, int curr)
{
    assert(curr < formulas.size());
    vec<PTRef> coll_f_args;

    // compute coll_f as (a_1^0 /\ ... /\ a_{n_1}^0) /\ ... /\ (a_1^{curr} /\ ... /\ a_{n_k}^{curr})
    for (int i = 0; i < curr+1; i++)
    {
        for (int j = 0; j < formulas[i].size(); j++)
            coll_f_args.push(formulas[i][j]);
    }
    PTRef coll_f = getLogic().mkAnd(coll_f_args);

    PTRef trans = logic.learnEqTransitivity(coll_f);
    if (trans != PTRef_Undef) {
        coll_f = getLogic().mkAnd(coll_f, trans);
    }
    bool res = computeSubstitutions(coll_f, formulas[curr]);
    return res;
}

