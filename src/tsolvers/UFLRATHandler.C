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

void UFLRATHandler::fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs)
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
                    deductions.push({lrasolver->getId(), l_Undef});
                refs.insert(tr, v);
            }
        }
        else if (logic.isNumEq(tr)) {
            vec<PTRef> args;
            Pterm& p = logic.getPterm(tr);
            args.push(p[0]);
            args.push(p[1]);
            char* msg;
            PTRef i1 = logic.mkNumLeq(args, &msg);
            PTRef i2 = logic.mkNumGeq(args, &msg);
            // These can simplify to true and false, and we don't
            // want them to LRA solver
            if (!refs.has(i1) && logic.isNumLeq(i1)) {
                declareAtom(i1);
                Var v = tmap.addBinding(i1);
                while (deductions.size() <= v)
                    deductions.push(DedElem(lrasolver->getId(), l_Undef));
                refs.insert(i1, v);
            }
            if (!refs.has(i2) && logic.isNumLeq(i2)) {
                declareAtom(i2);
                Var v = tmap.addBinding(i2);
                while (deductions.size() <= v)
                    deductions.push(DedElem(lrasolver->getId(), l_Undef));
                refs.insert(i2, v);
            }
        } else {
            // UF term
            if (!refs.has(tr)) {
                Pterm& t = logic.getPterm(tr);
                if (logic.getSym(t.symb()).rsort() != logic.getSort_bool())
                    continue;
                declareAtom(tr);
                Var v = tmap.addBinding(tr);
                while (deductions.size() <= v)
                    deductions.push({lrasolver->getId(), l_Undef});
                refs.insert(tr,v);
            }
        }
    }
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

