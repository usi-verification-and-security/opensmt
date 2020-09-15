#include "UFLRATHandler.h"
#include "lrasolver/LRASolver.h"
#include "TreeOps.h"
//#include "InterpolatingEgraph.h"
#include "Egraph.h"

UFLRATHandler::UFLRATHandler(SMTConfig & c, LRALogic & l)
        : LRATHandler(c, l)
        , logic(l)
{
    lrasolver = new LRASolver(config, logic);
    SolverId lra_id = lrasolver->getId();
    tsolvers[lra_id.id] = lrasolver;
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

PTRef UFLRATHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels)
{
    throw std::logic_error("Not implemented");
}

