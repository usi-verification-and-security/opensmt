#include "Theory.h"

bool LRATheory::simplify(PTRef root, PTRef &root_out)
{
    PTRef extra_root, extra_extra_root;
    lralogic.conjoinItes(root, extra_root);
    computeSubstitutions(extra_root, extra_extra_root);
    lralogic.simplifyAndSplitEq(extra_extra_root, root_out);
    return true;
}


