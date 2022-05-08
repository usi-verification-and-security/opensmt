#include "TSolverHandler.h"
#include "TreeOps.h"
#include "TResult.h"

TSolverHandler::~TSolverHandler()
{
    for (int i = 0; i < tsolvers.size(); i++) {
        delete tsolvers[i];
    }
}

void TSolverHandler::computeModel()
{
    for (int i = 0; i < tsolvers.size(); i++)
        if (tsolvers[i] != nullptr)
            tsolvers[i]->computeModel();
}

void TSolverHandler::fillTheoryFunctions(ModelBuilder & modelBuilder) const {
    for (auto index : solverSchedule) {
        auto * solver = tsolvers[index];
        assert(solver);
        solver->fillTheoryFunctions(modelBuilder);
    }
}

bool TSolverHandler::wouldDeduce(PtAsgn asgn){
    bool res = false;
    // Push backtrack points and the assignments to the theory solvers
    // according to the schedule
    for (int i = 0; i < solverSchedule.size(); i++) {
        int idx = solverSchedule[i];
        assert(tsolvers[idx] != nullptr);
        if(tsolvers[idx]->isKnown(asgn.tr)){
            bool res_new = tsolvers[idx]->wouldDeduce(asgn);
            res = res_new;
            return res;
        }
    }
    return res;
}

bool TSolverHandler::assertLit(PtAsgn asgn)
{
    bool res = true;
    // Push backtrack points and the assignments to the theory solvers
    // according to the schedule
    for (int i = 0; i < solverSchedule.size(); i++) {
        int idx = solverSchedule[i];
        assert(tsolvers[idx] != nullptr);
        tsolvers[idx]->pushBacktrackPoint();
        if (!tsolvers[idx]->isKnown(asgn.tr)) {
            continue;
        }
        bool res_new = tsolvers[idx]->assertLit(asgn);
        res &= res_new;
    }
    return res;
}


// Clear the vars of the solvers
void TSolverHandler::clearSolver()
{
    for (int i = 0; i < tsolvers.size(); i++)
        if (tsolvers[i] != NULL)
            tsolvers[i]->clearSolver();
}

void TSolverHandler::declareAtom(PTRef tr) {
    for (int i = 0; i < tsolvers.size(); i++) {
        if (tsolvers[i] != nullptr && tsolvers[i]->isValid(tr)) {
            tsolvers[i]->declareAtom(tr);
        }
    }
}

void TSolverHandler::informNewSplit(PTRef tr)
{
    for (int i = 0; i < tsolvers.size(); i++) {
        if (tsolvers[i] != NULL) {
                if (tsolvers[i]->isValid(tr)) {
                    tsolvers[i]->informNewSplit(tr);
            }
        }
    }
}

TRes TSolverHandler::check(bool complete)
{
    TRes res_final = TRes::SAT;
    for (int i = 0; i < tsolvers.size(); i++) {
        if (tsolvers[i] != NULL) {
            TRes res = tsolvers[i]->check(complete);
            if (res == TRes::UNSAT)
                return TRes::UNSAT;
            else if (res == TRes::UNKNOWN)
                res_final = TRes::UNKNOWN;
        }
    }

    return res_final;
}

vec<PTRef> TSolverHandler::getSplitClauses() {
    vec<PTRef> split_terms;
    for (int i = 0; i < tsolvers.size(); i++) {
        if (tsolvers[i] != nullptr && tsolvers[i]->hasNewSplits()) {
            tsolvers[i]->getNewSplits(split_terms);
            break;
        }
    }
    return split_terms;
}

// MB: This is currently needed to replace a common array of deduced elements with solver ID
TSolver* TSolverHandler::getReasoningSolverFor(PTRef ptref) const {
    assert(getLogic().isTheoryTerm(ptref));
    // MB: Can we use solverSchedule? Double check this if theory combination is implemented
    for (auto* solver : tsolvers) {
        if (solver != nullptr && solver->isValid(ptref)) {
            return solver;
        }
    }
    assert(false);
    return nullptr;
}



