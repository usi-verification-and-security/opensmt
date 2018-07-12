#include "TSolverHandler.h"
#include "TreeOps.h"
#include "TSolver.h"

TSolverHandler::~TSolverHandler()
{
    for (int i = 0; i < tsolvers.size(); i++)
        if (tsolvers[i] != NULL) delete tsolvers[i];
}

void TSolverHandler::computeModel()
{
    for (int i = 0; i < tsolvers.size(); i++)
        if (tsolvers[i] != NULL)
            tsolvers[i]->computeModel();
}

bool TSolverHandler::assertLit(PtAsgn asgn)
{
    bool res = true;
    // Push backtrack points and the assignments to the theory solvers
    // according to the schedule
    for (int i = 0; i < solverSchedule.size(); i++) {
        int idx = solverSchedule[i];
        assert(tsolvers[idx] != NULL);
        tsolvers[idx]->pushBacktrackPoint();
        if (!tsolvers[idx]->isKnown(asgn.tr)) {
            continue;
        }
        bool res_new = tsolvers[idx]->assertLit(asgn);
        res = (res == false) ? false : res_new;
    }
    return res;
}

// Declare a tree of terms
void TSolverHandler::declareTermTree(PTRef tr)
{
    vec<PtChild> terms;
    getTermList(tr, terms, getLogic());

    Map<PTRef,bool,PTRefHash> tr_map;
    for (int i = 0; i < terms.size(); i++)
    {
        if (!tr_map.has(terms[i].tr))
        {
            declareTerm(terms[i].tr);
            tr_map.insert(terms[i].tr, true);
        }
    }
}


char* TSolverHandler::printValue(PTRef tr)
{
    char* out = (char*)malloc(1);
    out[0] = '\0';
    for (int i = 0; i < tsolvers.size(); i++) {
        if (tsolvers[i] != NULL) {
            char* old_out = out;
            asprintf(&out, "%s\n%s", old_out, tsolvers[i]->printValue(tr));
            free(old_out);
        }
    }
    return out;
}

// Clear the vars of the solvers
void TSolverHandler::clearSolver()
{
    for (int i = 0; i < tsolvers.size(); i++)
        if (tsolvers[i] != NULL)
            tsolvers[i]->clearSolver();
}

// Declare term to the appropriate solver
void TSolverHandler::declareTerm(PTRef tr)
{
    for (int i = 0; i < tsolvers.size(); i++) {
        if (tsolvers[i] != NULL) {
//            printf("Thinking of declaring %s\n", getLogic().printTerm(tr));
                if (tsolvers[i]->isValid(tr)) {
                    tsolvers[i]->declareTerm(tr);
//                    printf("Declaring %s since it's my style\n", getLogic().printTerm(tr));
            }
            else {
//                printf("Not declaring %s since it's not my style\n", getLogic().printTerm(tr));
            }
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
        if (tsolvers[i] != NULL) {
            PTRef tr_subst = tr;
            if (substs.has(tr) && (substs[tr].sgn == l_True)) {
                tr_subst = substs[tr].tr;
            }
            ValPair vp = tsolvers[i]->getValue(tr_subst);
            if (vp != ValPair_Undef) {
                vp.tr = tr;
                return vp;
            }
        }
    }
    return { tr, NULL }; // Value is unspecified in the model
}

bool TSolverHandler::check(bool complete)
{
    for (int i = 0; i < tsolvers.size(); i++)
        if (tsolvers[i] != NULL)
            if (tsolvers[i]->check(complete) == false)
                return false;

    return true;
}


char* TSolverHandler::printExplanation(PTRef tr)
{
    char* out = (char*)malloc(1);
    out[0] = '\0';
    for (int i = 0; i < tsolvers.size(); i++) {
        if (tsolvers[i] != NULL) {
            char* old_out = out;
            asprintf(&out, "%s\n%s", old_out, tsolvers[i]->printExplanation(tr));
            free(old_out);
        }
    }
    return out;
}

