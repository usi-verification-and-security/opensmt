#include "UFLATHandler.h"
#include "lasolver/LASolver.h"
#include "TreeOps.h"
#include "Egraph.h"

UFLATHandler::UFLATHandler(SMTConfig & c, ArithLogic & l)
        : TSolverHandler(c)
        , logic(l)
{
    lasolver = new LASolver(config, logic);
    SolverId lra_id = lasolver->getId();
    tsolvers[lra_id.id] = lasolver;
    solverSchedule.push(lra_id.id);

    ufsolver = new Egraph(config, logic);

    SolverId uf_id = ufsolver->getId();
    tsolvers[uf_id.id] = ufsolver;
    solverSchedule.push(uf_id.id);

}

PTRef UFLATHandler::getInterpolant(const ipartitions_t&, map<PTRef, icolor_t> *, PartitionManager &)
{
    throw std::logic_error("Not implemented");
}

lbool UFLATHandler::getPolaritySuggestion(PTRef pt) const {
    if (lasolver->isKnown(pt)) { return lasolver->getPolaritySuggestion(pt); }
    if (ufsolver->isKnown(pt)) { return ufsolver->getPolaritySuggestion(pt); }
    return l_Undef;
}

TRes UFLATHandler::check(bool full) {
    auto res = TSolverHandler::check(full);
    if (full and res == TRes::SAT) {
        equalitiesToPropagate.clear();
        ufsolver->collectEqualitiesFor(interfaceVars, equalitiesToPropagate);
        lasolver->collectEqualitiesFor(interfaceVars, equalitiesToPropagate);
    }
    return res;
}

void UFLATHandler::declareAtom(PTRef atom) {
    TSolverHandler::declareAtom(atom);
    if (logic.isEquality(atom)) {
        knownEqualities.insert(atom);
    }
}

vec<PTRef> UFLATHandler::getSplitClauses() {
    if (equalitiesToPropagate.size() == 0) {
        return {};
    }
    vec<PTRef> res;
    for (PTRef eq : equalitiesToPropagate) {
        if (knownEqualities.count(eq) != 0) {
            continue;
        }
        // create clauses corresponding to "x = y iff x >= y and x <= y"
        assert(logic.isNumEq(eq));
        PTRef lhs = logic.getPterm(eq)[0];
        PTRef rhs = logic.getPterm(eq)[1];
        assert((logic.isNumVar(lhs) or logic.isNumConst(lhs)) and (logic.isNumVar(rhs) or logic.isNumConst(rhs)));
        PTRef leq = logic.mkLeq(lhs, rhs);
        PTRef geq = logic.mkGeq(lhs, rhs);
        vec<PTRef> args = {eq, logic.mkNot(leq), logic.mkNot(geq)}; // trichotomy clause
        res.push(logic.mkOr(args));
        args.clear();
        args.push(logic.mkNot(eq));
        args.push(leq);
        res.push(logic.mkOr(args)); // x = y => x <= y
        args.last() = geq;
        res.push(logic.mkOr(std::move(args))); // x = y => x >= y
    }
    equalitiesToPropagate.clear();
    return res;
}

