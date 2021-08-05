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
    for (auto solver : tsolvers) {
        if (solver != nullptr) {
            solver->fillTheoryFunctions(modelBuilder);
        }
    }
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

ValPair TSolverHandler::getValue(PTRef tr) const
{
    for (int i = 0; i < tsolvers.size(); i++) {
        if (tsolvers[i] != nullptr) {
            PTRef tmp{PTRef_Undef};
            PTRef tr_subst = substs.peek(tr, tmp) ? tmp : tr;
            ValPair vp = tsolvers[i]->getValue(tr_subst);
            if (vp != ValPair_Undef) {
                vp.tr = tr;
                return vp;
            }
        }
    }
    return { tr, nullptr }; // Value is unspecified in the model
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



