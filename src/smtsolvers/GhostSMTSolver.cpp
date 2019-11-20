//
// Created by prova on 14.11.19.
//

#include "GhostSMTSolver.h"
#include <utility>

bool GhostSMTSolver::isGhost(Lit l)
{
    if (!theory_handler.isTheoryTerm(var(l))) return false;
    vec<CRef> &appearances = thLitToClauses[toInt(l)];
    int i;
    for (i = 0; i < appearances.size(); i++) {
        if (!satisfied(ca[appearances[i]])) {
            std::swap(appearances[0], appearances[i]);
            break;
        }
    }
    return i == appearances.size();
}

void GhostSMTSolver::newDecisionLevel()
{
    SimpSMTSolver::newDecisionLevel();
    ghostTrailLim.push(ghostTrail.size());
}

void GhostSMTSolver::cancelUntil(int level) {
    int prev_dl = decisionLevel();
    SimpSMTSolver::cancelUntil(level);
    if (prev_dl > level) {
        for (int c = ghostTrail.size() - 1; c >= ghostTrailLim[level]; c--) {
            insertVarOrder(ghostTrail[c]);
        }
        ghostTrail.shrink(ghostTrail.size() - ghostTrailLim[level]);
        ghostTrailLim.shrink(ghostTrailLim.size() - level);
    }
    assert(ghostTrailLim.size() == trail_lim.size());
}

void
GhostSMTSolver::attachClause(CRef in_clause)
{
    SimpSMTSolver::attachClause(in_clause);

    if (in_clause == CRef_Undef)
        return;

    const Clause& c = ca[in_clause];
    if (c.learnt())
        return;

    for (int i = 0; i < c.size(); i++) {
        Lit l = c[i];
        if (theory_handler.isTheoryTerm(var(l))) {
            int idx = toInt(l);
            assert(idx < thLitToClauses.size());
            thLitToClauses[idx].push(in_clause);
        }
    }
}

void
GhostSMTSolver::detachClause(CRef cr, bool strict)
{
    SimpSMTSolver::detachClause(cr, strict);
    const Clause& c = ca[cr];
    if (c.learnt())
        return;

    assert(false);
    for (int i = 0; i < c.size(); i++) {
        Lit l = c[i];
        if (theory_handler.isTheoryTerm(var(l))) {
            int idx = toInt(l);
            assert(idx < thLitToClauses.size());
            // We need a better data structure
//            thLitToClauses[idx].pop();
        }
    }
}

Var
GhostSMTSolver::newVar(bool polarity, bool dvar)
{
    Var v = SimpSMTSolver::newVar(polarity, dvar);
    int idx = toInt(mkLit(v, true)); // true polarity has higher index
    while (thLitToClauses.size() <= idx)
        thLitToClauses.push();
    return v;
}

// Random decision:
Var
GhostSMTSolver::pickRandomBranchVar() {
    if (order_heap.empty())
        return var_Undef;
    else
        return order_heap[irand(random_seed,order_heap.size())];
}

// Activity based decision:
Var
GhostSMTSolver::pickBranchVar() {
    Var next;
    while (true) {
        if (order_heap.empty()) {
            next = var_Undef;
            break;
        }
        else {
            next = order_heap.removeMin();
        }
        if (value(next) == l_Undef && decision[next])
            break;
    }
    assert(next == var_Undef || value(next) == l_Undef);
    return next;
}

Lit
GhostSMTSolver::pickBranchPolarity(Var next) {
    assert(next != var_Undef);
    assert(value(next) == l_Undef);

    Lit choice = lit_Undef;

    bool sign = false;
    bool use_theory_suggested_polarity = config.use_theory_polarity_suggestion();

    if (use_theory_suggested_polarity && theory_handler.isTheoryTerm(next)) {
        lbool suggestion = this->theory_handler.getSolverHandler().getPolaritySuggestion(this->theory_handler.varToTerm(next));
        if (suggestion != l_Undef) {
            sign = (suggestion != l_True);
        }
    }
    else {
        switch (polarity_mode) {
            case polarity_true:
                sign = false;
                break;
            case polarity_false:
                sign = true;
                break;
            case polarity_user:
                sign = polarity[next];
                break;
            case polarity_rnd:
                sign = irand(random_seed, 2);
                break;
            default:
                assert(false);
        }
    }

    Lit l = mkLit(next, sign);
    if (isGhost(l)) {
        if (isGhost(~l)) {
            ghostTrail.push(var(l));
            l = lit_Undef;
        }
        else
            l = ~l;
    }
    return l;
}

Lit
GhostSMTSolver::pickBranchLit() {
    opensmt::StopWatch s(branchTimer);
    if (forced_split != lit_Undef) {
        Lit fs = forced_split;
        forced_split = lit_Undef;
        return fs;
    }

    if ((drand(random_seed) < random_var_freq) && !order_heap.empty()) {
        Var v = pickRandomBranchVar();
        if (v != var_Undef && value(v) == l_Undef) {
            Lit l = pickBranchPolarity(v);
            if (l != lit_Undef) {
                rnd_decisions++;
                return l;
            }
        }
    }

    Lit l = lit_Undef;
    while (l == lit_Undef) {
        Var v = pickBranchVar();
        if (v == var_Undef)
            break; // There are no free vars
        l = pickBranchPolarity(v);
    }

    return l;
}

void GhostSMTSolver::relocAll() {
    for (int i = 0; i < thLitToClauses.size(); i++) {
        vec<CRef> &appearances = thLitToClauses[i];
        for (int j = 0; j < appearances.size(); j++) {
            CRef cr = appearances[j];
            appearances[j] = ca[cr].relocation();
        }
    }
}

void
GhostSMTSolver::garbageCollect()
{
    ClauseAllocator to(ca.size() - ca.wasted());
    cleanUpClauses();
    to.extra_clause_field = ca.extra_clause_field; // NOTE: this is important to keep (or lose) the extra fields.

    SimpSMTSolver::relocAll(to);
    CoreSMTSolver::relocAll(to);
    relocAll();

    to.moveTo(ca);
}

void GhostSMTSolver::verifyModel()
{
    bool failed = false;
    for (int i = 0; i < clauses.size(); i++)
    {
        assert(ca[clauses[i]].mark() == 0);
        Clause& c = ca[clauses[i]];
        for (int j = 0; j < c.size(); j++)
            if (modelValue(c[j]) == l_True)
                goto next;

        for (int j = 0; j < c.size(); j++)
            if (modelValue(c[j]) == l_Undef && isGhost(c[j]))
                goto next;

        reportf("unsatisfied clause: ");
        printClause<Clause>(ca[clauses[i]]);
        reportf("\n");
        failed = true;
        next:;
    }

    assert(!failed);

    // Removed line
    // reportf("Verified %d original clauses.\n", clauses.size());
}

