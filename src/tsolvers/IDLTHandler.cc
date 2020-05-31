//
// Created by Martin Blicha on 10.05.20.
//

#include "IDLTHandler.h"
#include "LIALogic.h"
#include "stpsolver/STPSolver.h"
#include "TreeOps.h"

IDLTHandler::IDLTHandler(SMTConfig& c, LIALogic& l, vec<DedElem>& d, TermMapper& tmap)
        : TSolverHandler(c, d, tmap)
        , logic(l)
{
    stpsolver = new STPSolver(config, logic, deductions);
    SolverId my_id = stpsolver->getId();
    tsolvers[my_id.id] = stpsolver;
    solverSchedule.push(my_id.id);
}

IDLTHandler::~IDLTHandler() {
    delete stpsolver;
}

Logic &IDLTHandler::getLogic()
{
    return logic;
}

const Logic &IDLTHandler::getLogic() const
{
    return logic;
}

void IDLTHandler::fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs)
{
    // XXX Reorganize so that the storing of the previous variable would
    // not be so awkward?
    vec<PtChild> terms;
    getTermList(root, terms, getLogic());

    for (int i = 0; i < terms.size(); i++)
    {
        PTRef tr = terms[i].tr;
        if (logic.isNumLeq(tr)) {
            if (!refs.has(tr)) {
                declareAtom(tr);
                Var v = tmap.addBinding(tr);
                while (deductions.size() <= v)
                    deductions.push({stpsolver->getId(), l_Undef});
                refs.insert(tr, v);
            }
        }
        else if (logic.isNumEq(tr)) {
            vec<PTRef> args;
            Pterm& p = logic.getPterm(tr);
            args.push(p[0]);
            args.push(p[1]);
            PTRef i1 = logic.mkNumLeq(args);
            PTRef i2 = logic.mkNumGeq(args);
            // These can simplify to true and false, and we don't
            // want them to LRA solver
            if (!refs.has(i1) && logic.isNumLeq(i1)) {
                declareAtom(i1);
                Var v = tmap.addBinding(i1);
                while (deductions.size() <= v)
                    deductions.push(DedElem(stpsolver->getId(), l_Undef));
                refs.insert(i1, v);
            }
            if (!refs.has(i2) && logic.isNumLeq(i2)) {
                declareAtom(i2);
                Var v = tmap.addBinding(i2);
                while (deductions.size() <= v)
                    deductions.push(DedElem(stpsolver->getId(), l_Undef));
                refs.insert(i2, v);
            }
        } else {
            // A variable.  Will be handled as a part of an equality or
            // inequality.
            // assert(false); // Not an equality or inequality
        }
    }
}

bool IDLTHandler::assertLit_special(PtAsgn a)
{
    assert(a.sgn == l_True);
    if (logic.isNumEq(a.tr)) {
        Pterm& p = logic.getPterm(a.tr);
        vec<PTRef> args;
        args.push(p[0]);
        args.push(p[1]);
        PTRef i1 = logic.mkNumLeq(args);
        PTRef i2 = logic.mkNumGeq(args);
        bool res = assertLit(PtAsgn(i1, l_True));
        return res && assertLit(PtAsgn(i2, l_True));
    }
    else
        return assertLit(a);
}