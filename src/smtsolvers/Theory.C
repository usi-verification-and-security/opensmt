/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
 *********************************************************************/

#include "CoreSMTSolver.h"
#include "THandler.h"

// Stress test the theory solver
void CoreSMTSolver::crashTest(int rounds, Var var_true, Var var_false) {
    srand(0);
    for (int i = 1; i < nVars(); i++) {
        int stack_sz = 0;
        vec<Lit> tmp_trail; // <- add literals here
        for (int j = 0; j < rounds; j++) {
            // clause lengths
            for (int k = stack_sz; k < i; k++) {
                Var v = rand() % nVars();
                if (v == var_true) {
                    Lit l(v, false);
                    tmp_trail.push(l);
                }
                else if (v == var_false) {
                    Lit l(v, true);
                    tmp_trail.push(l);
                }
                else {
                    Lit l(v, rand() % 2);
                    tmp_trail.push(l);
                }
            }
            printf("Stack contains %d literals of which %d new\n", tmp_trail.size(), tmp_trail.size()-stack_sz);
            stack_sz = tmp_trail.size_();
            bool res = theory_handler.assertLits(tmp_trail);
                int new_stack_sz;
            if (res == false) {
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

int CoreSMTSolver::checkTheory( bool complete )
{
  // Skip calls to theory solvers
  // (does not seem to be helpful ...)
  if ( !complete
      && skipped_calls + config.sat_initial_skip_step < skip_step )
  {
    skipped_calls ++;
    return 1;
  }

  skipped_calls = 0;

  bool res = theory_handler.assertLits(trail)
          && theory_handler.check(complete, trail);
  //
  // Problem is T-Satisfiable
  //
  if ( res )
  {
    // Increments skip step for sat calls
    skip_step *= config.sat_skip_step_factor;

    if ( config.sat_theory_propagation > 0 )
    {
      if ( !complete )
      {
        int ded = deduceTheory( );
        assert( ded == 0 || ded == 1 );
        // There are deductions
        if ( ded )
        {
          res = theory_handler.assertLits(trail)
             && theory_handler.check(false, trail);

          // SAT and deductions done, time for BCP
          if ( res ) return 2;
          // Otherwise goto Problem is T-Unsatisfiable
          // This case can happen only during DTC
          assert( res == 0 );
          assert( ( ( config.logic == QF_UFIDL
                   || config.logic == QF_UFLRA )
                   && config.sat_lazy_dtc != 0 )
               || config.logic == QF_AXDIFF
               || config.logic == QF_AX );
        }
        // SAT and there are no deductions, time for decision
        else
        {
          skip_step *= config.sat_skip_step_factor;
          return 1; // SAT and nothing to deduce, time for decision
        }
      }
      else
        return 1; // SAT and complete call, we are done
    }
    else
    {
      skip_step *= config.sat_skip_step_factor;
      return 1; // Sat and nothing to deduce, time for decision
    }
  }
  //
  // Problem is T-Unsatisfiable
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
  vec< Lit > conflicting;
  vec< Lit > learnt_clause;
  int        max_decision_level;
  int        backtrack_level;

#ifdef PEDANTIC_DEBUG
  theory_handler.getConflict(conflicting, level, max_decision_level, assigns, trail);
#else
  theory_handler.getConflict(conflicting, level, max_decision_level, assigns);
#endif
#if PRODUCE_PROOF
  Enode * interp = NULL;
  if ( config.produce_inter > 0 )
    interp = theory_handler.getInterpolants( );
#endif

  assert( max_decision_level <= decisionLevel( ) );
  cancelUntil( max_decision_level );

  if ( decisionLevel( ) == 0 )
  {
#ifdef PRODUCE_PROOF
    // This case is equivalent to "Did not find watch" in propagate( )
    // All conflicting atoms are dec-level 0
    Clause * confl = Clause_new( conflicting, config.sat_temporary_learn );

    Clause & c = *confl;
    proof.addRoot( confl, CLA_THEORY );
    tleaves.push( confl );
    if ( config.incremental )
    {
      undo_stack_oper.push_back( NEWPROOF );
      undo_stack_elem.push_back( (void *)confl );
    }
    if ( config.produce_inter > 0 )
    {
      assert( interp );
      clause_to_in[ confl ] = interp;
      if ( config.incremental )
      {
	undo_stack_oper.push_back( NEWINTER );
	undo_stack_elem.push_back( NULL );
      }
    }
    proof.beginChain( confl );
    for ( int k = 0; k < c.size() ; k ++ )
    {
      assert( level[ var(c[k]) ] == 0 );
      assert( value( c[k] ) == l_False );
      assert( units[var(c[k])] != NULL );
      proof.resolve( units[var(c[k])], var(c[k]) );
    }
    // Empty clause derived
    proof.endChain( NULL );
#endif
    return -1;
  }

  Clause * confl = NULL;
  assert( conflicting.size( ) > 0 );

#ifdef PRODUCE_PROOF
  // Do not store theory lemma
  if ( conflicting.size( ) > config.sat_learn_up_to_size
    || conflicting.size( ) == 1 ) // That might happen in bit-vector theories
  {
    confl = Clause_new( conflicting );
  }
  // Learn theory lemma
  else
  {
    confl = Clause_new( conflicting, config.sat_temporary_learn );
    learnts.push(confl);
#ifndef SMTCOMP
    if ( config.incremental )
    {
      undo_stack_oper.push_back( NEWLEARNT );
      undo_stack_elem.push_back( (void *)confl );
    }
#endif
    attachClause(*confl);
    claBumpActivity(*confl);
    learnt_t_lemmata ++;
    if ( !config.sat_temporary_learn )
      perm_learnt_t_lemmata ++;
  }
#else
  // Do not store theory lemma
  if ( conflicting.size( ) > config.sat_learn_up_to_size
    || conflicting.size( ) == 1 ) // That might happen in bit-vector theories
  {
    confl = Clause_new( conflicting );
  }
  // Learn theory lemma
  else
  {
    confl = Clause_new( conflicting, config.sat_temporary_learn );
    learnts.push(confl);
#ifndef SMTCOMP
//    if ( config.incremental )
//    {
//      undo_stack_oper.push_back( NEWLEARNT );
//      undo_stack_elem.push_back( (void *)confl );
//    }
#endif
    attachClause(*confl);
    claBumpActivity(*confl);
    learnt_t_lemmata ++;
    if ( !config.sat_temporary_learn )
      perm_learnt_t_lemmata ++;
  }
#endif
  assert( confl );

  learnt_clause.clear();
#ifdef PRODUCE_PROOF
  proof.addRoot( confl, CLA_THEORY );
  tleaves.push( confl );
  if ( config.incremental )
  {
    undo_stack_oper.push_back( NEWPROOF );
    undo_stack_elem.push_back( (void *)confl );
  }
  if ( config.produce_inter > 0 )
  {
    assert( interp );
    clause_to_in[ confl ] = interp;
    if ( config.incremental )
    {
      undo_stack_oper.push_back( NEWINTER );
      undo_stack_elem.push_back( NULL );
    }
  }
#endif

  analyze( confl, learnt_clause, backtrack_level );

#ifndef PRODUCE_PROOF
  // Get rid of the temporary lemma
  if ( conflicting.size( ) > config.sat_learn_up_to_size )
  {
    free(confl);
  }
#endif

  cancelUntil(backtrack_level);
  assert(value(learnt_clause[0]) == l_Undef);

  if (learnt_clause.size() == 1){
    uncheckedEnqueue(learnt_clause[0]);
#ifdef PRODUCE_PROOF
    // Create a unit for the proof
    Clause * c = Clause_new( learnt_clause, false );
    proof.endChain( c );
    assert( units[ var(learnt_clause[0]) ] == NULL );
    units[ var(learnt_clause[0]) ] = proof.last( );
#endif
  }else{
    // ADDED FOR NEW MINIMIZATION
    learnts_size += learnt_clause.size( );
    all_learnts ++;

    Clause * c = Clause_new( learnt_clause, true );

#ifdef PRODUCE_PROOF
    proof.endChain( c );
    if ( config.incremental )
    {
      undo_stack_oper.push_back( NEWPROOF );
      undo_stack_elem.push_back( (void *)c );
    }
#endif
    learnts.push(c);
#ifndef SMTCOMP
    undo_stack_oper.push_back( NEWLEARNT );
    undo_stack_elem.push_back( (void *)c );
#endif
    attachClause(*c);
    claBumpActivity(*c);
    uncheckedEnqueue(learnt_clause[0], c);
  }

  varDecayActivity();
  claDecayActivity();

#ifdef PRODUCE_PROOF
  assert( proof.checkState( ) );
#endif

  return 0;
}
//
// Functions for lemma on demand modulo equality
//
int CoreSMTSolver::checkAxioms( )
{
  for ( ; axioms_checked < axioms.size( )
      ; axioms_checked ++ )
  {
    Clause * ax_ = axioms[ axioms_checked ];
    Clause & ax = *ax_;

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
	if ( level[ var(ax[i]) ] > max_decision_level )
	  max_decision_level = level[ var(ax[i]) ];
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

int CoreSMTSolver::analyzeUnsatLemma( Clause * confl )
{
  assert( confl );

#ifndef PRODUCE_PROOF
  if ( decisionLevel( ) == 0 )
    return -1;
#endif

  Clause & c = *confl;

  // Get highest decision level
  int max_decision_level = level[ var(c[0]) ];
  for ( int i = 1 ; i < c.size( ) ; i++ )
    if ( level[ var(c[i]) ] > max_decision_level )
      max_decision_level = level[ var(c[i]) ];

  cancelUntil( max_decision_level );

  if ( decisionLevel( ) == 0 )
  {
#ifdef PRODUCE_PROOF
    proof.beginChain( confl );
    for ( int k = 0; k < c.size() ; k ++ )
    {
      assert( level[ var(c[k]) ] == 0 );
      assert( value( c[k] ) == l_False );
      assert( units[ var(c[k]) ] != NULL );
      proof.resolve( units[var(c[k])], var(c[k]) );
    }
    // Empty clause reached
    proof.endChain( NULL );
#endif
    return -1;
  }

  vec< Lit > learnt_clause;
  int backtrack_level;
  analyze( confl, learnt_clause, backtrack_level );
  cancelUntil(backtrack_level);
  assert(value(learnt_clause[0]) == l_Undef);

  if (learnt_clause.size() == 1){
    uncheckedEnqueue(learnt_clause[0]);
#ifdef PRODUCE_PROOF
    // Create a unit for proof
    Clause * c = Clause_new( learnt_clause, false );
    proof.endChain( c );
    assert( units[ var(learnt_clause[0]) ] == NULL );
    units[ var(learnt_clause[0]) ] = proof.last( );
#endif
  }else{
	// ADDED FOR NEW MINIMIZATION
	learnts_size += learnt_clause.size( );
	all_learnts ++;

	Clause * c = Clause_new( learnt_clause, true );

#ifdef PRODUCE_PROOF
    proof.endChain( c );
    if ( config.incremental )
    {
      undo_stack_oper.push_back( NEWPROOF );
      undo_stack_elem.push_back( (void *)c );
    }
#endif
    learnts.push(c);
#ifndef SMTCOMP
    undo_stack_oper.push_back( NEWLEARNT );
    undo_stack_elem.push_back( (void *)c );
#endif
    attachClause(*c);
    claBumpActivity(*c);
    uncheckedEnqueue(learnt_clause[0], c);
  }

  varDecayActivity();
  claDecayActivity();

  return 0;
}

//
// Return values
// 0 no deductions done
// 1 some deductions done
//
int CoreSMTSolver::deduceTheory( )
{
  Lit ded = theory_handler.getDeduction( );

  if ( ded == lit_Undef )
    return 0;

  do
  {
#ifndef PRODUCE_PROOF
    if ( decisionLevel( ) == 0 )
      uncheckedEnqueue( ded );
    else
    {
#endif
      uncheckedEnqueue( ded, fake_clause );
#ifndef PRODUCE_PROOF
    }
#endif

    ded = theory_handler.getDeduction( );
  }
  while( ded != lit_Undef );
  return 1;
}
