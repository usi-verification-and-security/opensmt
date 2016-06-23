#include "UFTHandler.h"

UFTHandler::UFTHandler(SMTConfig& c, Logic& l, vec<DedElem>& d)
    : TSolverHandler(c, d)
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
            // It is possible that the term already has a variable from
            // a previous check-sat, if we are in incremental mode.
            Var v = (logic.getPterm(tr).getVar());
            if (v != var_Undef) {
                while (deductions.size() <= v)
                    deductions.push({getId(), l_Undef});
            } else {
                v = deductions.size();
                deductions.push({getId(), l_Undef});
                logic.getPterm(tr).setVar(deductions.size());
            }
            refs.insert(tr,v);
            deductions[v] = DedElem(getId(), l_Undef);
        }
    }
}


