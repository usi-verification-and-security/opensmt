#include "UFTHandler.h"
#include "TreeOps.h"
#include "Egraph.h"
#include "InterpolatingEgraph.h"

UFTHandler::UFTHandler(SMTConfig & c, Logic & l)
    : TSolverHandler(c)
    , logic(l)
{
    egraph = config.produce_inter() ? new InterpolatingEgraph(config, logic)
            : new Egraph(config, logic);
    setSolverSchedule({egraph});
}

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

PTRef UFTHandler::getInterpolant(const ipartitions_t& mask, ItpColorMap * labels, PartitionManager &pmanager)
{
    InterpolatingEgraph* iegraph = dynamic_cast<InterpolatingEgraph*>(egraph);
    assert(iegraph);
    return iegraph->getInterpolant(mask, labels, pmanager);
}
