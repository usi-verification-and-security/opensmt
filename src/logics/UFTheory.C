#include "Theory.h"

bool UFTheory::simplify(PTRef root, PTRef& root_out)
{
    return computeSubstitutionFixpoint(root, root_out);
}

