#include "UFLRATHandler.h"
#include "lrasolver/LRASolver.h"
#include "TreeOps.h"
#ifdef PRODUCE_PROOF
#include "InterpolatingEgraph.h"
#else // PRODUCE_PROOF
#include "Egraph.h"
#endif // PRODUCE_PROOF

UFLRATHandler::UFLRATHandler(SMTConfig& c, LRALogic& l, vec<DedElem>& d, TermMapper& tmap)
        : LRATHandler(c, l, d, tmap)
        , logic(l)
{
    lrasolver = new LRASolver(config, logic, deductions);
    SolverId lra_id = lrasolver->getId();
    tsolvers[lra_id.id] = lrasolver;
    solverSchedule.push(lra_id.id);

#ifdef PRODUCE_PROOF
    ufsolver = new InterpolatingEgraph(config, logic, deductions);
#else // PRODUCE_PROOF
    ufsolver = new Egraph(config, logic, deductions);
#endif // PRODUCE_PROOF

    SolverId uf_id = ufsolver->getId();
    tsolvers[uf_id.id] = ufsolver;
    solverSchedule.push(uf_id.id);

}

UFLRATHandler::~UFLRATHandler() {}

Logic &UFLRATHandler::getLogic()
{
    return logic;
}

#ifdef PRODUCE_PROOF
PTRef UFLRATHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels)
    {
        InterpolatingEgraph* iegraph = dynamic_cast<InterpolatingEgraph*>(ufsolver);
        assert(iegraph);
        return iegraph->getInterpolant(mask, labels);
    }
#endif

