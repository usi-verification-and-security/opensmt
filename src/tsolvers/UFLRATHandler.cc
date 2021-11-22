#include "UFLRATHandler.h"
#include "lasolver/LASolver.h"
#include "TreeOps.h"
//#include "InterpolatingEgraph.h"
#include "Egraph.h"

UFLRATHandler::UFLRATHandler(SMTConfig & c, ArithLogic & l)
        : LATHandler(c, l)
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

UFLRATHandler::~UFLRATHandler() {}

Logic &UFLRATHandler::getLogic()
{
    return logic;
}

PTRef UFLRATHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &pmanager)
{
    throw std::logic_error("Not implemented");
}

