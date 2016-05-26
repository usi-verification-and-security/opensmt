#ifndef THEORY_INTERPOLATOR_H
#define THEORY_INTERPOLATOR_H

#include "Global.h"
#include "PtStore.h"

class TheoryInterpolator
{
public:
    virtual PTRef getInterpolant(const ipartitions_t&) = 0;
};

#endif //THEORY_INTERPOLATOR_H
