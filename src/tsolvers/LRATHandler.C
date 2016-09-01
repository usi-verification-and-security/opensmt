#include "LRATHandler.h"


LRATHandler::LRATHandler(SMTConfig& c, LRALogic& l, vec<DedElem>& d, TermMapper& tmap)
        : TSolverHandler(c, d, l, tmap)
        , logic(l)
{
    lrasolver = new LRASolver(config, logic, deductions);
    my_id = lrasolver->getId();
    tsolvers[my_id.id] = lrasolver;
    solverSchedule.push(my_id.id);
}

LRATHandler::~LRATHandler() { }

Logic &LRATHandler::getLogic()
{
    return logic;
}

void LRATHandler::fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs)
{
    // XXX Reorganize so that the storing of the previous variable would
    // not be so awkward?
    vec<PtChild> terms;
    getTermList(root, terms, getLogic());

    for (int i = 0; i < terms.size(); i++)
    {
        PTRef tr = terms[i].tr;
        if (logic.isRealLeq(tr)) {
            if (!refs.has(tr)) {
                declareTerm(tr);
                // It is possible that the term already has a variable from
                // a previous check-sat, if we are in incremental mode.
                // In this case we need to restore the variable instead of
                // clearing it later.
                Var v = (logic.getPterm(tr).getVar());
                if (old_vars.has(tr))
                    old_vars.remove(tr);
                old_vars.insert(tr, v);
                if (v != var_Undef) {
                    while (deductions.size() <= v)
                        deductions.push({getId(), l_Undef});
                } else {
                    v = deductions.size();
                    deductions.push({getId(), l_Undef});
                    logic.getPterm(tr).setVar(deductions.size());
                }
                refs.insert(tr, deductions.size());
                logic.getPterm(tr).setVar(deductions.size());
                deductions.push(DedElem(getId(), l_Undef));
            }
        }
        else if (logic.isRealEq(tr)) {
            vec<PTRef> args;
            Pterm& p = logic.getPterm(tr);
            args.push(p[0]);
            args.push(p[1]);
            char* msg;
            PTRef i1 = logic.mkRealLeq(args, &msg);
            PTRef i2 = logic.mkRealGeq(args, &msg);
            // These can simplify to true and false, and we don't
            // want them to LRA solver
            if (!refs.has(i1) && logic.isRealLeq(i1)) {
                refs.insert(i1, deductions.size());
                logic.getPterm(i1).setVar(deductions.size());
                deductions.push(DedElem(getId(), l_Undef));
                declareTerm(i1);
                // It is possible that the term already has a variable from
                // a previous check-sat, if we are in incremental mode.
                // In this case we need to restore the variable instead of
                // clearing it later.
                Var v = (logic.getPterm(i1).getVar());
                if (old_vars.has(i1))
                    old_vars.remove(i1);
                old_vars.insert(i1, v);
            }
            if (!refs.has(i2) && logic.isRealLeq(i2)) {
                refs.insert(i2, deductions.size());
                logic.getPterm(i2).setVar(deductions.size());
                deductions.push(DedElem(getId(), l_Undef));
                declareTerm(i2);
                // It is possible that the term already has a variable from
                // a previous check-sat, if we are in incremental mode.
                // In this case we need to restore the variable instead of
                // clearing it later.
                Var v = (logic.getPterm(i2).getVar());
                if (old_vars.has(i2))
                    old_vars.remove(i2);
                old_vars.insert(i2, v);
            }
        }
    }
}

bool LRATHandler::assertLit_special(PtAsgn a)
{
    assert(logic.isRealEq(a.tr) || logic.isRealLeq(a.tr));
    assert(a.sgn == l_True);
    bool res = true;
    if (logic.isRealEq(a.tr)) {
        Pterm& p = logic.getPterm(a.tr);
        vec<PTRef> args;
        args.push(p[0]);
        args.push(p[1]);
        char* msg;
        PTRef i1 = logic.mkRealLeq(args, &msg);
        PTRef i2 = logic.mkRealGeq(args, &msg);
        res &= assertLit(PtAsgn(i1, l_True));
        res &= assertLit(PtAsgn(i2, l_True));
    }
    else
        res = assertLit(a);
    return res;
}


