#include "UFTHandler.h"
#include "TreeOps.h"
#ifdef PRODUCE_PROOF
#include "InterpolatingEgraph.h"
#else // PRODUCE_PROOF
#include "Egraph.h"
#endif // PRODUCE_PROOF

UFTHandler::UFTHandler(SMTConfig& c, Logic& l, vec<DedElem>& d, TermMapper& tmap)
    : TSolverHandler(c, d, tmap)
    , logic(l)
{
#ifdef PRODUCE_PROOF
    egraph = new InterpolatingEgraph(config, logic, deductions);
#else // PRODUCE_PROOF
    egraph = new Egraph(config, logic, deductions);
#endif // PRODUCE_PROOF

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

#ifdef PRODUCE_PROOF
PTRef UFTHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels)
{
    InterpolatingEgraph* iegraph = dynamic_cast<InterpolatingEgraph*>(egraph);
    assert(iegraph);
    return iegraph->getInterpolant(mask, labels);
}

#endif


