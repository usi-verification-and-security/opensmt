#include "UFLATHandler.h"
#include "lasolver/LASolver.h"
#include "egraph/Egraph.h"
#include "arraysolver/ArraySolver.h"

#include <common/TreeOps.h>

namespace opensmt {

UFLATHandler::UFLATHandler(SMTConfig & c, ArithLogic & l)
        : TSolverHandler(c)
        , logic(l)
{
    lasolver = new LASolver(config, logic);
    ufsolver = new Egraph(config, logic);
    arraySolver = logic.hasArrays() ? new ArraySolver(l, *ufsolver, c) : nullptr;
    if (logic.hasArrays()) {
        setSolverSchedule({ufsolver, arraySolver, lasolver});
    } else {
        setSolverSchedule({ufsolver,lasolver});
    }

}

PTRef UFLATHandler::getInterpolant(const ipartitions_t&, ItpColorMap *, PartitionManager &)
{
    throw std::logic_error("Not implemented");
}

lbool UFLATHandler::getPolaritySuggestion(PTRef pt) const {
    if (lasolver->isInformed(pt)) { return lasolver->getPolaritySuggestion(pt); }
    if (ufsolver->isInformed(pt)) { return ufsolver->getPolaritySuggestion(pt); }
    return l_Undef;
}

TRes UFLATHandler::check(bool full) {
    auto res = TSolverHandler::check(full);
    if (full and res == TRes::SAT and not lasolver->hasNewSplits() and (not arraySolver or not arraySolver->hasNewSplits())) {
        equalitiesToPropagate = ufsolver->collectEqualitiesFor(interfaceVars, equalitiesWithAddedInterfaceClauses);
        // MB: Only collect equalities from LASolver if there are none from UF solver.
        //  This prevents duplication of equalities
        if (equalitiesToPropagate.size() == 0) {
            equalitiesToPropagate = lasolver->collectEqualitiesFor(interfaceVars, equalitiesWithAddedInterfaceClauses);
        }
    }
    return res;
}

namespace {
    void addInterfaceClausesForEquality(ArithLogic & logic, PTRef eq, vec<PTRef> & clauses) {
        // create clauses corresponding to "x = y iff x >= y and x <= y"
        assert(logic.isNumEq(eq));
        PTRef lhs = logic.getPterm(eq)[0];
        PTRef rhs = logic.getPterm(eq)[1];
        assert((logic.isNumVar(lhs) or logic.isNumConst(lhs)) and (logic.isNumVar(rhs) or logic.isNumConst(rhs)));
        PTRef leq = logic.mkLeq(lhs, rhs);
        PTRef geq = logic.mkGeq(lhs, rhs);
        vec<PTRef> args = {eq, logic.mkNot(leq), logic.mkNot(geq)}; // trichotomy clause
        clauses.push(logic.mkOr(args));
        args.clear();
        args.push(logic.mkNot(eq));
        args.push(leq);
        clauses.push(logic.mkOr(args)); // x = y => x <= y
        args.last() = geq;
        clauses.push(logic.mkOr(std::move(args))); // x = y => x >= y
    }
}

vec<PTRef> UFLATHandler::getSplitClauses() {
    assert(not ufsolver->hasNewSplits());
    vec<PTRef> res;
    if (lasolver->hasNewSplits()) {
        lasolver->getNewSplits(res);
        return res;
    }
    if (arraySolver and arraySolver->hasNewSplits()) {
        auto isInterfaceVar = [this](PTRef term) { return logic.isVar(term) or logic.isNumConst(term); };
        arraySolver->getNewSplits(res);
        vec<PTRef> arrayLemmas;
        res.copyTo(arrayLemmas);
        // HACK: If array solver needs to decide equality on interface vars, we need to add corresponding lemmas already here
        for (PTRef lemma : arrayLemmas) {
            if (logic.isOr(lemma)) {
                for (PTRef lit : logic.getPterm(lemma)) {
                    PTRef atom = logic.isNot(lit) ? logic.getPterm(lit)[0] : lit;
                    if (logic.isNumEq(atom) and equalitiesWithAddedInterfaceClauses.find(atom) == equalitiesWithAddedInterfaceClauses.end()) {
                        PTRef lhs = logic.getPterm(atom)[0];
                        PTRef rhs = logic.getPterm(atom)[1];
                        if (isInterfaceVar(lhs) and isInterfaceVar(rhs)) {
                            addInterfaceClausesForEquality(logic, atom, res);
                            equalitiesWithAddedInterfaceClauses.insert(atom);
                        }
                    }
                }
            }
        }
        return res;
    }
    for (PTRef eq : equalitiesToPropagate) {
        if (auto [_, inserted] = equalitiesWithAddedInterfaceClauses.insert(eq); inserted) {
            addInterfaceClausesForEquality(logic, eq, res);
        }
    }
    equalitiesToPropagate.clear();
    return res;
}

void UFLATHandler::fillTheoryFunctions(ModelBuilder & modelBuilder) const {
    // MB: To properly build model in UF solver, we already need values for the LA variables from LA solver.
    lasolver->fillTheoryFunctions(modelBuilder);
    ufsolver->fillTheoryFunctions(modelBuilder);
}

}
