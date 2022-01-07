#include "UFLATHandler.h"
#include "lasolver/LASolver.h"
#include "TreeOps.h"
#include "Egraph.h"
#include "InterpolatingEgraph.h"

UFLATHandler::UFLATHandler(SMTConfig & c, ArithLogic & l)
        : TSolverHandler(c)
        , logic(l)
{
    lasolver = new LASolver(config, logic);
    SolverId lra_id = lasolver->getId();
    tsolvers[lra_id.id] = lasolver;
    solverSchedule.push(lra_id.id);

    ufsolver = config.produce_inter() > 0 ? new InterpolatingEgraph(config, logic)
                                          : new Egraph(config, logic);

    SolverId uf_id = ufsolver->getId();
    tsolvers[uf_id.id] = ufsolver;
    solverSchedule.push(uf_id.id);

}

PTRef UFLATHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> * labels, PartitionManager & pmanager)
{
    assert(lasolver->hasExplanation() or ufsolver->hasExplanation());
    if (lasolver->hasExplanation()) {
        if (logic.hasReals() and not logic.hasIntegers()) {
            return lasolver->getRealInterpolant(mask, labels, pmanager);
        } else if (logic.hasIntegers() and not logic.hasReals()) {
            if (labels == nullptr) {
                throw OsmtInternalException("LIA interpolation requires partitioning map, but no map was provided");
            }
            return lasolver->getIntegerInterpolant(*labels);
        } else {
            throw OsmtInternalException("Mixed arithmetic interpolation not supported yet");
        }
    }
    if (ufsolver->hasExplanation()) {
        InterpolatingEgraph* iegraph = dynamic_cast<InterpolatingEgraph*>(ufsolver);
        assert(iegraph);
        return iegraph->getInterpolant(mask, labels, pmanager);
    }
    throw OsmtInternalException("Unexpected situation in UFLATHandler::getInterpolant");
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
        ufsolver->collectEqualitiesFor(interfaceVars, equalitiesToPropagate, knownEqualities);
        lasolver->collectEqualitiesFor(interfaceVars, equalitiesToPropagate, knownEqualities);
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

