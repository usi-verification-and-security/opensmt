//
// Created by Antti on 21.10.21.
//

#include "LATHandler.h"
#include "lasolver/LASolver.h"

#include <common/InternalException.h>
#include <common/TreeOps.h>

namespace opensmt {

LATHandler::LATHandler(SMTConfig & c, ArithLogic & l)
    : TSolverHandler(c)
    , logic(l)
{
    lasolver = new LASolver(config, logic);
    setSolverSchedule({lasolver});
}

PTRef LATHandler::getInterpolantImpl(ipartitions_t const & mask, ItpColorMap * labels, PartitionManager & pmanager) {
    if (logic.hasReals() and not logic.hasIntegers()) {
        return lasolver->getRealInterpolant(mask, labels, pmanager);
    } else if (logic.hasIntegers() and not logic.hasReals()) {
        if (labels == nullptr) {
            throw InternalException("LIA interpolation requires partitioning map, but no map was provided");
        }
        return lasolver->getIntegerInterpolant(*labels);
    } else {
        throw InternalException("Mixed arithmetic interpolation not supported yet");
    }
}

}
