#include "tsolvers/TSolverHandler.h"

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
        if(!tr_map.contains(terms[i].tr))
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

// Declare term to the appropriate solver
void TSolverHandler::declareTerm(PTRef tr)
{
    for (int i = 0; i < tsolvers.size(); i++)
        if (tsolvers[i] != NULL)
            tsolvers[i]->declareTerm(tr);
}

ValPair TSolverHandler::getValue(PTRef tr) const
{
    for (int i = 0; i < tsolvers.size(); i++)
        if (tsolvers[i] != NULL) {
            ValPair vp = tsolvers[i]->getValue(tr);
            if (vp != ValPair_Undef)
                return vp;
        }
    return ValPair(tr, "unknown");
}

bool TSolverHandler::check(bool complete)
{
    int i = 0;
    for (; i < tsolvers.size(); i++)
        if (tsolvers[i] != NULL && tsolvers[i]->check(complete) == false) return false;

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

