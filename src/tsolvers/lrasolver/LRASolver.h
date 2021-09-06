#ifndef LRASOLVER_H
#define LRASOLVER_H

#include <PartitionManager.h>
#include "LRALogic.h"
#include "LASolver.h"


//
// Class to solve Linear Arithmetic theories
//

class LRASolver: public LASolver
{

public:

    LRASolver(SMTConfig & c, LRALogic & l);

    ~LRASolver( ) = default;



public:
    PTRef getInterpolant(const ipartitions_t &, map<PTRef, icolor_t>*, PartitionManager & pmanager);
};

#endif
