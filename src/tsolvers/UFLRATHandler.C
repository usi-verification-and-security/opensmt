#include "UFLRATHandler.h"

UFLRATHandler::UFLRATHandler(SMTConfig& c, LRALogic& l, vec<DedElem>& d, TermMapper& tmap)
        : LRATHandler(c, l, d, tmap)
        , logic(l)
{
    lrasolver = new LRASolver(config, logic, deductions);
    SolverId lra_id = lrasolver->getId();
    tsolvers[lra_id.id] = lrasolver;
    solverSchedule.push(lra_id.id);

    ufsolver = new Egraph(config, logic, deductions);
    SolverId uf_id = ufsolver->getId();
    tsolvers[uf_id.id] = ufsolver;
    solverSchedule.push(uf_id.id);

}

UFLRATHandler::~UFLRATHandler() {}

Logic &UFLRATHandler::getLogic()
{
    return logic;
}


