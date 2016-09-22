#include "UFLRATheory.h"

bool UFLRATheory::simplify(vec<PFRef>& formulas, int curr)
{
    // Take care of UF simplifications as well
    return LRATheory::simplify(formulas, curr);
}
