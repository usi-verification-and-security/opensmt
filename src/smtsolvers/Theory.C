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

#include "CoreSMTSolver.h"

#ifdef PRODUCE_PROOF
#include "Proof.h"
#endif //PRODUCE_PROOF

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

TPropRes CoreSMTSolver::checkTheory(bool complete, int& conflictC)
{
    // Skip calls to theory solvers
    // (does not seem to be helpful ...)
    if ( !complete
            && skipped_calls + config.sat_initial_skip_step < skip_step )
    {
        skipped_calls ++;
        return tpr_Decide;
    }

    skipped_calls = 0;

    bool res = theory_handler.assertLits(trail)
               && theory_handler.check(complete);
    //
    // Problem is T-Satisfiable
    //
    if ( res )
    {
        // Increments skip step for sat calls
        skip_step *= config.sat_skip_step_factor;

        vec<Lit> new_splits; // In case the theory is not convex the new split var is inserted here
        theory_handler.getNewSplits(new_splits);



        if (new_splits.size() > 0) {
            printf(" -> Adding the new split\n");

            vec<LitLev> deds;
            deduceTheory(deds); // To remove possible theory deductions

            Lit l1 = new_splits[0];
            Lit l2 = new_splits[1];

            assert(safeValue(l1) == l_Undef || safeValue(l2) == l_Undef);
            assert(safeValue(l1) != l_True);
            assert(safeValue(l2) != l_True);

            if (safeValue(l1) == l_Undef && safeValue(l2) == l_Undef) {
                addSMTClause_(new_splits);
                forced_split = ~l1;
                return tpr_Decide;
            }
            else {

                Lit l_f = value(l1) == l_False ? l1 : l2; // false literal
                Lit l_i = value(l1) == l_False ? l2 : l1; // implied literal

                int lev = vardata[var(l_f)].level;
                cancelUntil(lev);
                CRef cr;
                addSMTClause_(new_splits, cr);
                if (decisionLevel() > 0) {
                    // DL0 implications are already enqueued in addSMTClause_
                    assert(cr != CRef_Undef);
                    uncheckedEnqueue(l_i, cr);
                }
                return tpr_Propagate;
            }
        }
        vec<LitLev> deds;
        deduceTheory(deds); // deds will be ordered by decision levels
        for (int i = 0; i < deds.size(); i++)
        {
            if (deds[i].lev != decisionLevel()) {
                // Maybe do something someday?
            }
            uncheckedEnqueue(deds[i].l, CRef_Fake);
        }
        if (deds.size() > 0)
        {
            return 0;
        }
        else
        {
            skip_step *= config.sat_skip_step_factor;
            return tpr_Decide; // Sat and nothing to deduce, time for decision
        }
    }
    //
    // Query is T-Unsatisfiable
    //
    assert( res == 0 );
    // Reset skip step for uns calls
    skip_step = config.sat_initial_skip_step;

#ifndef PRODUCE_PROOF
    // Top-level conflict, problem is T-Unsatisfiable
    if ( decisionLevel( ) == 0 )
        return -1;
#endif

    conflicts++;
    conflictC++;
    vec< Lit > conflicting;
    vec< Lit > learnt_clause;
    int        max_decision_level;
    int        backtrack_level;

#ifdef PEDANTIC_DEBUG
    theory_handler.getConflict(conflicting, vardata, max_decision_level, trail);
#else
    theory_handler.getConflict(conflicting, vardata, max_decision_level);
#endif
#if PRODUCE_PROOF
    /*
    PTRef interp = PTRef_Undef;
    if ( config.produce_inter() > 0 )
        interp = theory_handler.getInterpolants( );
    */
#endif

    assert( max_decision_level <= decisionLevel( ) );
    cancelUntil( max_decision_level );

    if ( decisionLevel( ) == 0 )
    {
#ifdef PRODUCE_PROOF
        // This case is equivalent to "Did not find watch" in propagate( )
        // All conflicting atoms are dec-level 0
        CRef confl = ca.alloc(conflicting, config.sat_temporary_learn);

        Clause & c = ca[confl];
        proof.addRoot( confl, CLA_THEORY );
        //TODO: is it correct?
        //proof.setTheoryInterpolator(confl, theory_itpr);
        //clause_to_itpr[ confl ] = theory_itpr;
        tleaves.push( confl );
        if ( config.isIncremental() )
        {
            // Not yet integrated
            //assert(false);
            undo_stack.push(undo_stack_el(undo_stack_el::NEWPROOF, confl));
        }
        if ( config.produce_inter() > 0 )
        {
            //assert(interp != PTRef_Undef);
            // FIXME why here?
            //proof.resolve( units[var(c[k])], var(c[k]) );
        }
        // Empty clause derived
        // ADDED CODE BEGIN
        proof.beginChain( confl );
        for ( int k = 0; k < c.size() ; k ++ )
        {
            //assert( level[ var(c[k]) ] == 0 );
            //assert( value( c[k] ) == l_False );
            //assert( units[var(c[k])] != NULL );
            proof.resolve( units[var(c[k])], var(c[k]) );
        }
        // ADDED CODE END
        proof.endChain( CRef_Undef );
#endif
        return tpr_Unsat;
    }

    CRef confl = CRef_Undef;
    assert( conflicting.size( ) > 0 );

#ifdef PRODUCE_PROOF
    // Do not store theory lemma
    if ( conflicting.size( ) > config.sat_learn_up_to_size
            || conflicting.size( ) == 1 ) // That might happen in bit-vector theories
    {
        confl = ca.alloc(conflicting);
    }
    // Learn theory lemma
    else
    {
        confl = ca.alloc(conflicting, config.sat_temporary_learn);
        learnts.push(confl);
        if ( config.isIncremental() )
        {
            undo_stack.push(undo_stack_el(undo_stack_el::NEWLEARNT, confl));
        }
        attachClause(confl);
        claBumpActivity(ca[confl]);
        learnt_t_lemmata ++;
        if ( !config.sat_temporary_learn )
            perm_learnt_t_lemmata ++;
    }
#else
    // Do not store theory lemma
    if ( conflicting.size( ) > config.sat_learn_up_to_size
            || conflicting.size( ) == 1 ) // That might happen in bit-vector theories
    {
        confl = ca.alloc(conflicting);
    }
    // Learn theory lemma
    else
    {
        confl = ca.alloc(conflicting, config.sat_temporary_learn);
        learnts.push(confl);
//    if ( config.incremental )
//    {
//      undo_stack_oper.push_back( NEWLEARNT );
//      undo_stack_elem.push_back( (void *)confl );
//    }
        attachClause(confl);
        claBumpActivity(ca[confl]);
        learnt_t_lemmata ++;
        if ( !config.sat_temporary_learn )
            perm_learnt_t_lemmata ++;
    }
#endif
    assert( confl != CRef_Undef );

    learnt_clause.clear();
#ifdef PRODUCE_PROOF
    proof.addRoot( confl, CLA_THEORY );
    tleaves.push( confl );
    if ( config.isIncremental() )
    {
        undo_stack.push(undo_stack_el(undo_stack_el::NEWPROOF, confl));
    }
    if ( config.produce_inter() > 0 )
    {
        if ( config.isIncremental() )
        {
            undo_stack.push(undo_stack_el(undo_stack_el::NEWINTER, CRef_Undef));
        }
    }
#endif

    analyze( confl, learnt_clause, backtrack_level );

#ifndef PRODUCE_PROOF
    // Get rid of the temporary lemma
    if ( conflicting.size( ) > config.sat_learn_up_to_size )
    {
        ca.free(confl);
    }
#endif

    cancelUntil(backtrack_level);
    assert(value(learnt_clause[0]) == l_Undef);

    if (learnt_clause.size() == 1) {
        uncheckedEnqueue(learnt_clause[0]);
#ifdef PRODUCE_PROOF
        // Create a unit for the proof
        CRef cr = ca.alloc(learnt_clause, false);
        proof.endChain( cr );
        //assert( units[ var(learnt_clause[0]) ] == CRef_Undef );
        units[ var(learnt_clause[0]) ] = proof.last( );
#endif
    } else {
        // ADDED FOR NEW MINIMIZATION
        learnts_size += learnt_clause.size( );
        all_learnts ++;

        CRef cr = ca.alloc(learnt_clause, true);

#ifdef PRODUCE_PROOF
        proof.endChain( cr );
        if ( config.isIncremental() )
        {
            undo_stack.push(undo_stack_el(undo_stack_el::NEWPROOF, cr));
        }
#endif
        learnts.push(cr);
        learnt_theory_conflicts++;
        undo_stack.push(undo_stack_el(undo_stack_el::NEWLEARNT, cr));
        attachClause(cr);
        claBumpActivity(ca[cr]);
        uncheckedEnqueue(learnt_clause[0], cr);
    }

    varDecayActivity();
    claDecayActivity();

#ifdef PRODUCE_PROOF
    assert( proof.checkState( ) );
#endif

    return tpr_Propagate;
}

//
// Functions for lemma on demand modulo equality
//
int CoreSMTSolver::checkAxioms( )
{
    for ( ; axioms_checked < axioms.size( )
            ; axioms_checked ++ )
    {
        CRef ax_ = axioms[axioms_checked];
        Clause& ax = ca[ax_];

        int assigned_false = 0;
        Lit unassigned = lit_Undef;
        int max_decision_level = -1;

        for ( int i = 0 ; i < ax.size( ) ; i ++ )
        {
            if ( value( ax[ i ] ) == l_True )
                continue;

            if ( value( ax[ i ] ) == l_False )
            {
                assigned_false ++;
                if ( level( var(ax[i]) ) > max_decision_level )
                    max_decision_level = level( var(ax[i]) );
            }
            else
                unassigned = ax[ i ];
        }
        // All literals in lemma are false
        if ( assigned_false == ax.size( ) )
            return analyzeUnsatLemma( ax_ );
        // All literals but one are false: time for BCP
        if ( unassigned != lit_Undef
                && assigned_false == ax.size( ) - 1 )
        {
            // Determine the lowest decision level that
            // causes the propagation
            if ( decisionLevel( ) > max_decision_level )
                cancelUntil( max_decision_level );

            axioms_checked ++;
            uncheckedEnqueue( unassigned, ax_ );
            return 2;
        }
    }

    assert( axioms_checked == axioms.size( ) );

    return 1;
}

int CoreSMTSolver::analyzeUnsatLemma(CRef confl)
{
    assert(confl != CRef_Undef);

#ifndef PRODUCE_PROOF
  if ( decisionLevel( ) == 0 )
    return -1;
#endif

    Clause & c = ca[confl];

    // Get highest decision level
    int max_decision_level = level(var(c[0]));
    for ( int i = 1 ; i < c.size( ) ; i++ )
        if ( level(var(c[i])) > max_decision_level )
            max_decision_level = level(var(c[i]));

    cancelUntil( max_decision_level );

    if ( decisionLevel( ) == 0 )
    {
#ifdef PRODUCE_PROOF
        proof.beginChain( confl );
        for ( int k = 0; k < c.size() ; k ++ )
        {
            assert(level(var(c[k])) == 0);
            assert(value( c[k] ) == l_False);
            assert(units[ var(c[k]) ] != CRef_Undef);
            proof.resolve(units[var(c[k])], var(c[k]));
        }
        // Empty clause reached
        proof.endChain(CRef_Undef);
#endif
        return -1;
    }

    vec< Lit > learnt_clause;
    int backtrack_level;
    analyze( confl, learnt_clause, backtrack_level );
    cancelUntil(backtrack_level);
    assert(value(learnt_clause[0]) == l_Undef);

    if (learnt_clause.size() == 1)
    {
        uncheckedEnqueue(learnt_clause[0]);
#ifdef PRODUCE_PROOF
        // Create a unit for proof
        CRef cr = ca.alloc(learnt_clause, false);
        proof.endChain(cr);
        assert(units[var(learnt_clause[0])] == CRef_Undef);
        units[ var(learnt_clause[0]) ] = proof.last();
#endif
    }
    else
    {
        // ADDED FOR NEW MINIMIZATION
        learnts_size += learnt_clause.size( );
        all_learnts ++;

        CRef cr = ca.alloc(learnt_clause, true);

#ifdef PRODUCE_PROOF
        proof.endChain(cr);
        if ( config.isIncremental() )
            undo_stack.push(undo_stack_el(undo_stack_el::NEWPROOF, cr));
#endif
        learnts.push(cr);
        undo_stack.push(undo_stack_el(undo_stack_el::NEWLEARNT, cr));
        attachClause(cr);
        claBumpActivity(ca[cr]);
        uncheckedEnqueue(learnt_clause[0], cr);
    }

    varDecayActivity();
    claDecayActivity();

    return 0;
}

//
// Return a vector containing deduced literals and their decision levels
//
void CoreSMTSolver::deduceTheory(vec<LitLev>& deductions)
{
    Lit ded = lit_Undef;
    int n_deductions = 0;
    int last_dl = -1;

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
