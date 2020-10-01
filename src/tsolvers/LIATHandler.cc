#include "LIATHandler.h"
#include "TreeOps.h"
#include <liasolver/LIASolver.h>

LIATHandler::LIATHandler(SMTConfig & c, LIALogic & l)
        : TSolverHandler(c)
        , logic(l)
{
    liasolver = new LIASolver(config, logic);
    SolverId my_id = liasolver->getId();
    tsolvers[my_id.id] = liasolver;
    solverSchedule.push(my_id.id);
}

LIATHandler::~LIATHandler() { }

Logic &LIATHandler::getLogic()
{
    return logic;
}

const Logic &LIATHandler::getLogic() const
{
    return logic;
}

PTRef LIATHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &)
{
    throw std::logic_error{"Interpolation currently not supported in LIA"};
}
