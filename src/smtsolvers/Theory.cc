/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include <TSolver.h>
#include "CoreSMTSolver.h"
#include "Proof.h"

// Stress test the theory solver
void CoreSMTSolver::crashTest(int rounds, Var var_true, Var var_false)
{
    srand(0);
    for (int i = 1; i < nVars(); i++)
    {
        int stack_sz = 0;
        vec<Lit> tmp_trail; // <- add literals here
        for (int j = 0; j < rounds; j++)
        {
            // clause lengths
            for (int k = stack_sz; k < i; k++)
            {
                Var v = rand() % nVars();
                if (v == var_true)
                {
                    tmp_trail.push(mkLit(v, false));
                }
                else if (v == var_false)
                {
                    tmp_trail.push(mkLit(v, true));
                }
                else
                {
                    tmp_trail.push(mkLit(v, rand() % 2));
                }
            }
            printf("Stack contains %d literals of which %d new\n", tmp_trail.size(), tmp_trail.size()-stack_sz);
            stack_sz = tmp_trail.size_();
            bool res = theory_handler.assertLits(tmp_trail);
            int new_stack_sz;
            if (res == false)
            {
                printf("Conflict\n");
                new_stack_sz = 0;
            }
            else
                new_stack_sz = rand() % (i+1);

            theory_handler.backtrack(new_stack_sz);
            tmp_trail.shrink(stack_sz - new_stack_sz);
            stack_sz = new_stack_sz;
            assert(tmp_trail.size() == stack_sz);
        }
    }
}

TPropRes
CoreSMTSolver::handleSat()
{
    // Increments skip step for sat calls
    skip_step *= config.sat_skip_step_factor;

    vec<Lit> new_splits; // In case the theory is not convex the new split var is inserted here
    theory_handler.getNewSplits(new_splits);

    if (new_splits.size() > 0) {

        assert(new_splits.size() == 2); // For now we handle the binary case only.

        //printf(" -> Adding the new split\n");

        vec<LitLev> deds;
        deduceTheory(deds); // To remove possible theory deductions

        Lit l1 = new_splits[0];
        Lit l2 = new_splits[1];

        assert(safeValue(l1) == l_Undef || safeValue(l2) == l_Undef);
        assert(safeValue(l1) != l_True);
        assert(safeValue(l2) != l_True);
        // MB: ensure the solver knows about the variables
        addVar_(var(l1));
        addVar_(var(l2));
        if (safeValue(l1) == l_Undef && safeValue(l2) == l_Undef) {
            // MB: allocate, attach and remember the clause - treated as original
            // MB: TODO: why not theory clause?
            CRef cr = ca.alloc(new_splits, false);
            attachClause(cr);
            clauses.push(cr);
            if (this->logsProof()) {
                // MB: the proof needs to know about the new class; TODO: what type it should be?
                proof->newOriginalClause(cr);
            }
            forced_split = ~l1;
            return TPropRes::Decide;
        }
        else {
            Lit l_f = value(l1) == l_False ? l1 : l2; // false literal
            Lit l_i = value(l1) == l_False ? l2 : l1; // implied literal

            int lev = vardata[var(l_f)].level;
            cancelUntil(lev);
            if (!this->logsProof()) {
                if (decisionLevel() == 0) {
                    // MB: do not allocate, we can directly enqueue the implied literal
                    uncheckedEnqueue(l_i);
                    return TPropRes::Propagate;
                }
            }
            // MB: we are going to propagate, make sure the implied literal is the first one
            if (l_i != new_splits[0]) {
                new_splits[0] = l_i;
                new_splits[1] = l_f;
            }
            CRef cr = ca.alloc(new_splits, false);
            attachClause(cr);
            clauses.push(cr);
            if (logsProof()) {
                // MB: the proof needs to know about the new class; TODO: what type it should be?
                proof->newOriginalClause(cr);
            }
            uncheckedEnqueue(l_i, cr);
            return TPropRes::Propagate;
        }
    }
    if (config.sat_theory_propagation > 0) {
        vec<LitLev> deds;
        deduceTheory(deds); // deds will be ordered by decision levels
        for (int i = 0; i < deds.size(); i++) {
            if (deds[i].lev != decisionLevel()) {
                // Maybe do something someday?
            }
            uncheckedEnqueue(deds[i].l, CRef_Fake);
        }
        if (deds.size() > 0) {
            return TPropRes::Propagate;
        }
    }
    skip_step *= config.sat_skip_step_factor;
    return TPropRes::Decide; // Sat and nothing to deduce, time for decision
}

TPropRes
CoreSMTSolver::handleUnsat()
{
    //
    // Query is T-Unsatisfiable
    //

    // Reset skip step for uns calls
    skip_step = config.sat_initial_skip_step;

    if (!logsProof()) {
        // Top-level conflict, problem is T-Unsatisfiable
        if (decisionLevel() == 0) {
            return TPropRes::Unsat;
        }
    }
    vec< Lit > conflicting;
    vec< Lit > learnt_clause;
    int        max_decision_level;
    int        backtrack_level;

    theory_handler.getConflict(conflicting, vardata, max_decision_level);

    assert( max_decision_level <= decisionLevel( ) );
    cancelUntil( max_decision_level );

    if ( decisionLevel( ) == 0 )
    {
        if(logsProof()) {
            // All conflicting atoms are dec-level 0
            CRef confl = ca.alloc(conflicting, config.sat_temporary_learn);
            proof->newTheoryClause(confl);
            this->finalizeProof(confl);
        }
        return TPropRes::Unsat;
    }

    CRef confl = CRef_Undef;
    assert( conflicting.size( ) > 0 );

    bool learnOnlyTemporary = conflicting.size() > config.sat_learn_up_to_size;
    if (learnOnlyTemporary
            || conflicting.size( ) == 1 ) // That might happen in bit-vector theories
    {
        confl = ca.alloc(conflicting);
    }
    // Learn theory lemma
    else
    {
        confl = ca.alloc(conflicting, config.sat_temporary_learn);
        learnts.push(confl);
        attachClause(confl);
        claBumpActivity(ca[confl]);
        learnt_t_lemmata ++;
        if ( !config.sat_temporary_learn )
            perm_learnt_t_lemmata ++;
    }
    assert( confl != CRef_Undef );

    learnt_clause.clear();
    if (logsProof()) {
        proof->newTheoryClause(confl);
    }
    analyze( confl, learnt_clause, backtrack_level );

    if (!logsProof()) {
        // Get rid of the temporary lemma
        if (learnOnlyTemporary)
        {
            ca.free(confl);
        }
    }

    cancelUntil(backtrack_level);
    assert(value(learnt_clause[0]) == l_Undef);

    if (learnt_clause.size() == 1) {
        CRef reason = CRef_Undef;
        if (logsProof())
        {
            CRef cr = ca.alloc(learnt_clause, false);
            proof->endChain(cr);
            reason = cr;
        }
        uncheckedEnqueue(learnt_clause[0], reason);
    } else {
        // ADDED FOR NEW MINIMIZATION
        learnts_size += learnt_clause.size( );
        all_learnts ++;

        CRef cr = ca.alloc(learnt_clause, true);

        if (logsProof()) {
            proof->endChain(cr);
        }
        learnts.push(cr);
        learnt_theory_conflicts++;
        undo_stack.push(undo_stack_el(undo_stack_el::NEWLEARNT, cr));
        attachClause(cr);
        claBumpActivity(ca[cr]);
        uncheckedEnqueue(learnt_clause[0], cr);
    }

    varDecayActivity();
    claDecayActivity();
    return TPropRes::Propagate;
}

/**
 * Performs the consistency check of current assignment in the theory and returns the next action for the SAT solver.
 * TPropRes::Unsat - 0-level theory conflict has been detected, the whole problem is UNSAT
 * TPropRes::Propagate - New literal has been enqued to the trail, propagation phase should follow
 * TPropRes::Decide - Current assignment is consistent, no propagation detected, SAT solver should decide next variable
 *
 * Note that if theory conflict is detected, this conflict is handled in handleUnsat() method.
 * The solver can either backtrack to consistent state, learn theory clause and return TPropRes::Propagate
 * or if the conflict is on level 0, return TPropRes::Unsat to indicate that the whole problem is UNSAT
 *
 * @param complete should the theory check be complete or simpler (sound but not necessary complete) check can be used
 * @param conflictC conflict counter
 * @return The action SAT solver should perform next
 */
TPropRes CoreSMTSolver::checkTheory(bool complete, int& conflictC)
{
    // Skip calls to theory solvers
    // (does not seem to be helpful ...)
    if ( !complete
            && skipped_calls + config.sat_initial_skip_step < skip_step )
    {
        skipped_calls ++;
        return TPropRes::Decide;
    }

    skipped_calls = 0;

    TRes res = theory_handler.assertLits(trail) ? theory_handler.check(complete) : TRes::UNSAT;
    //
    // Problem is T-Satisfiable
    //
    if ( res == TRes::SAT )
        return handleSat();
    else if (res == TRes::UNSAT) {
        conflicts++;
        conflictC++;
        return handleUnsat();
    }
    assert(res == TRes::UNKNOWN);

    return TPropRes::Decide;
}

//
// Return a vector containing deduced literals and their decision levels
//
void CoreSMTSolver::deduceTheory(vec<LitLev>& deductions)
{
    Lit ded = lit_Undef;
    int n_deductions = 0;

    while (true)
    {
        ded = theory_handler.getDeduction();
        if (ded == lit_Undef)      break;
        if (value(ded) != l_Undef) continue;

        // Found an unassigned deduction
        n_deductions ++;

        deductions.push(LitLev(ded, decisionLevel()));
    }
#ifdef PEDANTIC_DEBUG
    int max_lev = -1;
    for (int i = 0; i < deductions.size(); i++) {
        if (deductions[i].lev < max_lev) {
            cerr << "Bling! Expected less than " << max_lev;
            cerr << " " << deductions[i].lev << endl;
        }
        max_lev = deductions[i].lev;
    }
#endif
    return;
}

#ifdef DEBUG_REASONS

void CoreSMTSolver::addTheoryReasonClause_debug(Lit ded, vec<Lit>& reason) {
    Clause* c = Clause_new<vec<Lit> >(reason);
    int idx = debug_reasons.size();
    debug_reasons.push(c);
    assert(!debug_reason_map.contains(var(ded)));
    debug_reason_map.insert(var(ded), idx);
    return;
}

void CoreSMTSolver::checkTheoryReasonClause_debug(Var v) {
    int idx = debug_reason_map[v];
    Clause* c = debug_reasons[idx];
    bool v_found = false;
    for (int i = 0; i < c->size(); i++) {
        Lit l = (*c)[i];
        Var u = var(l);
        if (value(l) != l_False && (v != u)) {
            cerr << theory_handler.printAsrtClause(c) << endl;
            assert(false);
        }
        assert(value(l) == l_False || (v == u));
        if (v == u) {
            v_found = true;
            if (value(l) != l_Undef) {
                cerr << theory_handler.printAsrtClause(c) << endl;
                assert(false);
            }
        }
    }
    assert(v_found);
    assert(var((*c)[0]) == v);
}

void CoreSMTSolver::removeTheoryReasonClause_debug(Var v) {
    int idx = debug_reason_map[v];
    assert(debug_reason_map.contains(v));
    debug_reason_map.remove(v);
    assert(!debug_reason_map.contains(v));
}

#endif
