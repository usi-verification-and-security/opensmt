#include "UFLRATHandler.h"
#include "lasolver/LASolver.h"
#include "TreeOps.h"
#include "Egraph.h"

UFLRATHandler::UFLRATHandler(SMTConfig & c, ArithLogic & l)
        : TSolverHandler(c)
        , logic(l)
{
    lasolver = new LASolver(config, logic);
    SolverId lra_id = lasolver->getId();
    tsolvers[lra_id.id] = lasolver;
    solverSchedule.push(lra_id.id);

    ufsolver = new Egraph(config, logic);

    SolverId uf_id = ufsolver->getId();
    tsolvers[uf_id.id] = ufsolver;
    solverSchedule.push(uf_id.id);

}

PTRef UFLRATHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &pmanager)
{
    throw std::logic_error("Not implemented");
}

