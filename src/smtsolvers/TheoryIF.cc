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

#include <algorithm>
#include <numeric>
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

namespace {
std::vector<int> sortByLastAssignedLevel(std::vector<vec<Lit>> & splitClauses, std::function<int(Var)> getVarLevel) {
    if (splitClauses.size() == 1) {
        return {0};
    }
    std::vector<int> lastAssignedLevels;
    lastAssignedLevels.resize(splitClauses.size(), 0);
    std::transform(splitClauses.begin(), splitClauses.end(), lastAssignedLevels.begin(), [&](auto const & clause) {
        auto maxLevel = 0;
        for (Lit l : clause) {
            auto level = getVarLevel(var(l));
            if (level > maxLevel) {
                maxLevel = level;
            }
        }
        return maxLevel;
    });

    std::vector<int> indices(splitClauses.size());
    std::iota(indices.begin(), indices.end(), 0);
    std::sort(indices.begin(), indices.end(), [&lastAssignedLevels](int first, int second) {
        return lastAssignedLevels[first] < lastAssignedLevels[second];
    });
    return indices;
}
}

TPropRes CoreSMTSolver::handleNewSplitClauses(SplitClauses & splitClauses) {
    vec<LitLev> deds;
    deduceTheory(deds); // To remove possible theory deductions
    TPropRes res = TPropRes::Undef;
    struct PropagationData {
        Lit lit;
        CRef reason;
    };
    std::vector<PropagationData> propData;

    auto processNewClause = [&] (auto const & clause) {
        CRef cr = ca.alloc(clause);
        attachClause(cr);
        clauses.push(cr);
        if (logsProofForInterpolation()) {
            // MB: the proof needs to know about the new clause
            proof->newSplitClause(cr);
        }
        return cr;
    };

    auto sortedIndices = sortByLastAssignedLevel(splitClauses, [this](Var v) { return v < nVars() ? vardata[v].level : 0; });

    for (int index : sortedIndices) {
        auto & splitClause = splitClauses[index];
        unsigned satisfied = 0;
        unsigned falsified = 0;
        unsigned unknown = 0;
        // MB: ensure the SAT solver knows about the variables and that they are active
        int impliedIndex = -1;
        for (int i = 0; i < splitClause.size(); ++i) {
            Lit l = splitClause[i];
            addVar_(var(l));
            if (value(l) == l_True) { ++satisfied; }
            else if (value(l) == l_False) { ++falsified; }
            else { ++unknown; impliedIndex = i; }
        }
        assert(satisfied != 0 or unknown != 0); // The clause cannot be falsified
        if (satisfied == 0 and unknown == 1) { // propagate
            // Find the lowest level where all the falsified literals are still falsified
            int backtrackLevel = 0;
            for (Lit l : splitClause) {
                if (value(l) == l_False and vardata[var(l)].level > backtrackLevel) {
                    backtrackLevel = vardata[var(l)].level;
                }
            }
            if (backtrackLevel < decisionLevel()) {
                assert(propData.empty()); // This should hold when clauses are sorted according to last assigned level
                propData.clear();         // But let's make sure
                cancelUntil(backtrackLevel);
            }
            if (!this->logsProofForInterpolation()) {
                if (decisionLevel() == 0) {
                    // MB: do not allocate, we can directly enqueue the implied literal
                    uncheckedEnqueue(splitClause[impliedIndex], CRef_Undef);
                    res = TPropRes::Propagate;
                    continue;
                }
            }
            // MB: we are going to propagate, make sure the implied literal is the first one
            Lit implied = splitClause[impliedIndex];
            std::swap(splitClause[0],splitClause[impliedIndex]);
            CRef cr = processNewClause(splitClause);
            propData.push_back(PropagationData{.lit = implied, .reason = cr});
            res = TPropRes::Propagate;
        } else {
            // MB: ensure that that the first literal is not falsified
            if (value(splitClause[0]) == l_False and impliedIndex != -1) {
                std::swap(splitClause[0],splitClause[impliedIndex]);
            }

            processNewClause(splitClause);
            if (satisfied == 0) {
                if (res != TPropRes::Propagate) {
                    res = TPropRes::Decide;
                }
            }
        }
    }
    assert(res != TPropRes::Undef);
    if (res == TPropRes::Propagate) {
        assert(std::all_of(propData.begin(), propData.end(), [this](auto const & datum){
            return value(var(datum.lit)) == l_Undef;
        }));
        for (auto [litToPropogate, reason] : propData) {
            // MB: same literal can be added multiple times, coming from different clauses
            if (value(litToPropogate) == l_Undef) {
                uncheckedEnqueue(litToPropogate, reason);
            } else {
                assert(value(litToPropogate) == l_True);
            }
        }
    }
    return res;
}

TPropRes
CoreSMTSolver::handleSat()
{
    // Increments skip step for sat calls
    skip_step *= config.sat_skip_step_factor;

    auto newSplitClauses = theory_handler.getNewSplits();

    if (not newSplitClauses.empty()) {
        return handleNewSplitClauses(newSplitClauses);
    }
    // Theory propagate
    vec<LitLev> deds;
    deduceTheory(deds); // deds will be ordered by decision levels
    for (int i = 0; i < deds.size(); i++) {
        Lit l = deds[i].l;
        if (deds[i].lev != decisionLevel()) {
            // Maybe do something someday?
        }
        CRef deducedReason = CRef_Fake;
        if (decisionLevel() == 0 and logsProofForInterpolation()) {
            vec<Lit> reasonLits;
            theory_handler.getReason(l, reasonLits);
            assert(reasonLits.size() > 0);
            CRef theoryReason = ca.alloc(reasonLits);
            CRef unit = ca.alloc(vec<Lit>{l});
            proof->newTheoryClause(theoryReason);
            proof->beginChain(theoryReason);
            Clause const & clause = ca[theoryReason];
            for (unsigned j = 0; j < clause.size(); ++j) {
                if (clause[j] != l) {
                    proof->addResolutionStep(reason(var(clause[j])), var(clause[j]));
                }
            }
            proof->endChain(unit);
            vardata[var(l)].reason = unit;
            deducedReason = unit;
        }
        uncheckedEnqueue(l, deducedReason);
    }
    if (deds.size() > 0) {
        return TPropRes::Propagate;
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

    if (!logsProofForInterpolation()) {
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
    for(Lit l: conflicting){
        Var v = var(l);
        PTRef atom = theory_handler.getTMap().varToPTRef(v);;
        assert(theory_handler.getLogic().isTheoryTerm(atom));
    }

    assert( max_decision_level <= decisionLevel( ) );
    cancelUntil( max_decision_level );

    if ( decisionLevel( ) == 0 )
    {
        if (logsProofForInterpolation()) {
            // All conflicting atoms are dec-level 0
            CRef confl = config.sat_temporary_learn ? ca.alloc(conflicting, {true, computeGlue(conflicting)}) : ca.alloc(conflicting);
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
    else {
        confl = config.sat_temporary_learn ? ca.alloc(conflicting, {true, computeGlue(conflicting)}) : ca.alloc(conflicting);
        learnts.push(confl);
        attachClause(confl);
        claBumpActivity(ca[confl]);
        learnt_t_lemmata ++;
        if ( !config.sat_temporary_learn )
            perm_learnt_t_lemmata ++;
    }
    assert( confl != CRef_Undef );

    learnt_clause.clear();
    if (logsProofForInterpolation()) {
        proof->newTheoryClause(confl);
    }
    analyze(confl, learnt_clause, backtrack_level);

    if (!logsProofForInterpolation()) {
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
        if (logsProofForInterpolation())
        {
            CRef cr = ca.alloc(learnt_clause);
            proof->endChain(cr);
            reason = cr;
        }
        uncheckedEnqueue(learnt_clause[0], reason);
    } else {
        // ADDED FOR NEW MINIMIZATION
        learnts_size += learnt_clause.size( );
        all_learnts ++;

        CRef cr = ca.alloc(learnt_clause, {true, computeGlue(learnt_clause)});

        if (logsProofForInterpolation()) {
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