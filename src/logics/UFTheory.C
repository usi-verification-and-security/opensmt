#include "Theory.h"

bool UFTheory::simplify(PTRef root, PTRef& root_out)
{
    return computeSubstitutions(root, root_out);
}

