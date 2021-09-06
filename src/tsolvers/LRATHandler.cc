#include "LRATHandler.h"

#include "TreeOps.h"
#include "lasolver/LASolver.h"
#include "LRALogic.h"

LRATHandler::LRATHandler(SMTConfig & c, LRALogic & l)
        : TSolverHandler(c)
        , logic(l)
{
    lasolver = new LASolver(config, logic);
    SolverId my_id = lasolver->getId();
    tsolvers[my_id.id] = lasolver;
    solverSchedule.push(my_id.id);
}

LRATHandler::~LRATHandler() { }

Logic &LRATHandler::getLogic()
{
    return logic;
}

const Logic &LRATHandler::getLogic() const
{
    return logic;
}

lbool LRATHandler::getPolaritySuggestion(PTRef p) const {
    return lasolver->getPolaritySuggestion(p);
}

PTRef LRATHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &pmanager)
{
    return lasolver->getInterpolant(mask, labels, pmanager);
}


