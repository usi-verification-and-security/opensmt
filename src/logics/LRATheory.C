#include "Theory.h"

bool LRATheory::simplify(vec<PushFrame>& formulas, int curr)
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

//    PTRef root_with_ites;
//    lralogic.conjoinItes(coll_f, root_with_ites);
    computeSubstitutions(coll_f, formulas[curr]);
    PTRef tmp;
    lralogic.simplifyAndSplitEq(formulas[curr].root, tmp);
    formulas[curr].root = tmp;
    return true;
}


