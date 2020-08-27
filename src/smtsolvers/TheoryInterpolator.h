#ifndef THEORY_INTERPOLATOR_H
#define THEORY_INTERPOLATOR_H

#include "Global.h"
#include "PtStore.h"
#include <PartitionManager.h>

class TheoryInterpolator
{
public:
    virtual PTRef getInterpolant(const ipartitions_t&, map<PTRef, icolor_t>*, PartitionManager &pmanager) = 0;
};

#endif //THEORY_INTERPOLATOR_H
