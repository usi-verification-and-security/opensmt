#include "Theory.h"

bool UFTheory::simplify(PTRef root, PTRef& root_out)
{
    PTRef trans = logic.learnEqTransitivity(root);
    if (trans != PTRef_Undef) {
        vec<PTRef> v;
        v.push(trans);
        v.push(root);
        root = logic.mkAnd(v);
    }
    return computeSubstitutions(root, root_out);
}

