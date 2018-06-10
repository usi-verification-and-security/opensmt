#include "LIATHandler.h"
#include "TreeOps.h"
#include "LIASolver.h"

LIATHandler::LIATHandler(SMTConfig& c, LIALogic& l, vec<DedElem>& d, TermMapper& tmap)
        : TSolverHandler(c, d, l, tmap)
        , logic(l)
{
    liasolver = new LIASolver(config, logic, deductions);
    SolverId my_id = liasolver->getId();
    tsolvers[my_id.id] = liasolver;
    solverSchedule.push(my_id.id);
}

LIATHandler::~LIATHandler() { }

Logic &LIATHandler::getLogic()
{
    return logic;
}

const Logic &LIATHandler::getLogic() const
{
    return logic;
}


void LIATHandler::fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs)
{
    // XXX Reorganize so that the storing of the previous variable would
    // not be so awkward?
    vec<PtChild> terms;
    getTermList(root, terms, getLogic());

    for (int i = 0; i < terms.size(); i++)
    {
        PTRef tr = terms[i].tr;
        if (logic.isIntLeq(tr)) {
            if (!refs.has(tr)) {
                declareTerm(tr);
                Var v = tmap.addBinding(tr);
                while (deductions.size() <= v)
                    deductions.push({liasolver->getId(), l_Undef});
                refs.insert(tr, v);
            }
        }
        else if (logic.isIntEq(tr)) {
            vec<PTRef> args;
            Pterm& p = logic.getPterm(tr);
            args.push(p[0]);
            args.push(p[1]);
            char* msg;
            PTRef i1 = logic.mkIntLeq(args, &msg);
            PTRef i2 = logic.mkIntGeq(args, &msg);
            // These can simplify to true and false, and we don't
            // want them to LRA solver
            if (!refs.has(i1) && logic.isIntLeq(i1)) {
                declareTerm(i1);
                Var v = tmap.addBinding(i1);
                while (deductions.size() <= v)
                    deductions.push(DedElem(liasolver->getId(), l_Undef));
                refs.insert(i1, v);
            }
            if (!refs.has(i2) && logic.isIntLeq(i2)) {
                declareTerm(i2);
                Var v = tmap.addBinding(i2);
                while (deductions.size() <= v)
                    deductions.push(DedElem(liasolver->getId(), l_Undef));
                refs.insert(i2, v);
            }
        } else {
            // A variable.  Will be handled as a part of an equality or
            // inequality.
            // assert(false); // Not an equality or inequality
        }
    }
}

bool LIATHandler::assertLit_special(PtAsgn a)
{
//    assert(logic.isRealEq(a.tr) || logic.isRealLeq(a.tr));
    assert(a.sgn == l_True);
    bool res = true;
    if (logic.isIntEq(a.tr)) {
        Pterm& p = logic.getPterm(a.tr);
        vec<PTRef> args;
        args.push(p[0]);
        args.push(p[1]);
        char* msg;
        PTRef i1 = logic.mkIntLeq(args, &msg);
        PTRef i2 = logic.mkIntGeq(args, &msg);
        res &= assertLit(PtAsgn(i1, l_True));
        res &= assertLit(PtAsgn(i2, l_True));
    }
    else
        res = assertLit(a);
    return res;
}

#ifdef PRODUCE_PROOF
PTRef LIATHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels)
{
    return liasolver->getInterpolant(mask, labels);
}
#endif // PRODUCE_PROOF
