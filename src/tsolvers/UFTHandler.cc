#include "UFTHandler.h"
#include "TreeOps.h"
#include "InterpolatingEgraph.h"
#include "Egraph.h"

UFTHandler::UFTHandler(SMTConfig& c, Logic& l, vec<DedElem>& d, TermMapper& tmap)
    : TSolverHandler(c, d, tmap)
    , logic(l)
{
    egraph = config.produce_proofs > 0 ? new InterpolatingEgraph(config, logic, deductions)
            : new Egraph(config, logic, deductions);

    SolverId my_id = egraph->getId();
    tsolvers[my_id.id] = egraph;
    solverSchedule.push(my_id.id); // Only UF for the QF_UF logic
}

UFTHandler::~UFTHandler() { }

bool UFTHandler::assertLit_special(PtAsgn a)
{
    return assertLit(a);
}

Logic &UFTHandler::getLogic()
{
    return logic;
}

const Logic &UFTHandler::getLogic() const
{
    return logic;
}

//
// Starting from the root, get all terms.  Get a variable for each term.
//
void UFTHandler::fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs)
{
    vec<PtChild> terms;
    getTermList(root, terms, getLogic());

    // We need to have a variable for each term for the theory solver to
    // work.
    for (int i = 0; i < terms.size(); i++)
    {
        PTRef tr = terms[i].tr;
        if (!refs.has(tr)) {
            Pterm& t = logic.getPterm(tr);
            if (logic.getSym(t.symb()).rsort() != logic.getSort_bool())
                continue;
            declareAtom(tr);
            Var v = tmap.addBinding(tr);
            while (deductions.size() <= v)
                deductions.push({egraph->getId(), l_Undef});
            refs.insert(tr,v);
        }
    }
}

lbool UFTHandler::getPolaritySuggestion(PTRef p) const {
    if (egraph) { return egraph->getPolaritySuggestion(p); }
    return l_Undef;
}

PTRef UFTHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels)
{
    InterpolatingEgraph* iegraph = dynamic_cast<InterpolatingEgraph*>(egraph);
    assert(iegraph);
    return iegraph->getInterpolant(mask, labels);
}

