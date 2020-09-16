#include "UFTHandler.h"
#include "TreeOps.h"
#include "Egraph.h"
#include "InterpolatingEgraph.h"

UFTHandler::UFTHandler(SMTConfig & c, Logic & l)
    : TSolverHandler(c)
    , logic(l)
{
    egraph = config.produce_inter() > 0 ? new InterpolatingEgraph(config, logic)
            : new Egraph(config, logic);

    SolverId my_id = egraph->getId();
    tsolvers[my_id.id] = egraph;
    solverSchedule.push(my_id.id); // Only UF for the QF_UF logic
}

UFTHandler::~UFTHandler() { }

Logic &UFTHandler::getLogic()
{
    return logic;
}

const Logic &UFTHandler::getLogic() const
{
    return logic;
}

lbool UFTHandler::getPolaritySuggestion(PTRef p) const {
    if (egraph) { return egraph->getPolaritySuggestion(p); }
    return l_Undef;
}

PTRef UFTHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &pmanager)
{
    InterpolatingEgraph* iegraph = dynamic_cast<InterpolatingEgraph*>(egraph);
    assert(iegraph);
    return iegraph->getInterpolant(mask, labels);
}

