#include "UFTHandler.h"

UFTHandler::UFTHandler(SMTConfig& c, Logic& l, vec<DedElem>& d, TermMapper& tmap)
    : TSolverHandler(c, d, l, tmap)
    , logic(l)
{
    egraph = new Egraph(config, logic, deductions);
    my_id = egraph->getId();
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

//
// Starting from the root, get all terms.  Get a variable for each term.
//
void UFTHandler::fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs)
{
    vec<PtChild> terms;
    getTermList(root, terms, getLogic());

    int n = deductions.size()-1;

    // We need to have a variable for each term for the theory solver to
    // work.
    for (int i = 0; i < terms.size(); i++)
    {
        PTRef tr = terms[i].tr;
        if (!refs.has(tr)) {
            declareTerm(tr);
            Pterm& t = logic.getPterm(tr);
            if (logic.getSym(t.symb()).rsort() != logic.getSort_bool())
                continue;
            Var v = tmap.addBinding(tr);
            while (deductions.size() <= v)
                deductions.push({getId(), l_Undef});
            refs.insert(tr,v);
        }
    }
}


