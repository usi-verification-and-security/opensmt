#include "LRATHandler.h"


LRATHandler::LRATHandler(SMTConfig& c, LRALogic& l, vec<DedElem>& d)
        : TSolverHandler(c, d)
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
    vec<PtChild> terms;
    getTermList(root, terms, getLogic());

    for (int i = 0; i < terms.size(); i++)
    {
        PTRef tr = terms[i].tr;
        if (logic.isRealLeq(tr)) {
            if (!refs.contains(tr)) {
                declareTerm(tr);
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
            if (!refs.contains(i1)) {
                refs.insert(i1, deductions.size());
                logic.getPterm(i1).setVar(deductions.size());
                deductions.push(DedElem(getId(), l_Undef));
                declareTerm(i1);
            }
            if (!refs.contains(i2)) {
                refs.insert(i2, deductions.size());
                logic.getPterm(i2).setVar(deductions.size());
                deductions.push(DedElem(getId(), l_Undef));
                declareTerm(i2);
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


