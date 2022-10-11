#include "TSolverHandler.h"
#include "TreeOps.h"
#include "TResult.h"

TSolverHandler::~TSolverHandler()
{
    for (auto id : solverSchedule) {
        delete tsolvers[id];
    }
}

void TSolverHandler::computeModel()
{
    for (auto id : solverSchedule) {
        tsolvers[id]->computeModel();
    }
}

void TSolverHandler::fillTheoryFunctions(ModelBuilder & modelBuilder) const {
    for (auto index : solverSchedule) {
        auto * solver = tsolvers[index];
        assert(solver);
        solver->fillTheoryFunctions(modelBuilder);
    }
}

bool TSolverHandler::assertLit(PtAsgn asgn)
{
    bool res = true;
    // Push backtrack points and the assignments to the theory solvers
    // according to the schedule
    for (auto id : solverSchedule) {
        assert(tsolvers[id] != nullptr);
        auto & solver = *tsolvers[id];
        solver.pushBacktrackPoint();
        if (not solver.isInformed(asgn.tr)) {
            continue;
        }
        bool res_new = solver.assertLit(asgn);
        res &= res_new;
    }
    return res;
}


// Clear the vars of the solvers
void TSolverHandler::clearSolver()
{
    for (auto id : solverSchedule) {
        auto & solver = *tsolvers[id];
        solver.clearSolver();
    }
}

void TSolverHandler::declareAtom(PTRef tr) {
    for (auto id : solverSchedule) {
        auto & solver = *tsolvers[id];
        if (solver.isValid(tr)) {
            solver.declareAtom(tr);
        }
    }
}

void TSolverHandler::informNewSplit(PTRef tr)
{
    for (auto id : solverSchedule) {
        auto & solver = *tsolvers[id];
        if (solver.isValid(tr)) {
            solver.informNewSplit(tr);
        }
    }
}

TRes TSolverHandler::check(bool complete)
{
    TRes res_final = TRes::SAT;
    for (auto id : solverSchedule) {
        auto & solver = *tsolvers[id];
        TRes res = solver.check(complete);
        if (res == TRes::UNSAT) {
            return TRes::UNSAT;
        } else if (res == TRes::UNKNOWN)
            res_final = TRes::UNKNOWN;
    }
    return res_final;
}

vec<PTRef> TSolverHandler::getSplitClauses() {
    vec<PTRef> split_terms;
    for (auto id : solverSchedule) {
        auto & solver = *tsolvers[id];
        if (solver.hasNewSplits()) {
            solver.getNewSplits(split_terms);
            break;
        }
    }
    return split_terms;
}

// MB: This is currently needed to replace a common array of deduced elements with solver ID
TSolver* TSolverHandler::getReasoningSolverFor(PTRef ptref) const {
    assert(getLogic().isTheoryTerm(ptref));
    // MB: Can we use solverSchedule? Double check this if theory combination is implemented
    for (auto id : solverSchedule) {
        auto & solver = *tsolvers[id];
        if (solver.isValid(ptref))
            return tsolvers[id];
    }
    assert(false);
    return nullptr;
}



