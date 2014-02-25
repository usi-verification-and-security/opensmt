/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2013, Antti Hyvarinen

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

/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

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

/****************************************************************************************[Solver.C]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "CoreSMTSolver.h"
//#include "THandler.h"
#include "Sort.h"
#include <cmath>

#ifndef OPTIMIZE
#include <iostream>
#include <fstream>
#include <sys/wait.h>
#endif

namespace opensmt
{
  extern bool stop;
}

//=================================================================================================
// Constructor/Destructor:


//CoreSMTSolver::CoreSMTSolver( Egraph & e, SMTConfig & c )
CoreSMTSolver::CoreSMTSolver(SMTConfig & c, THandler& t )
  // Initializes configuration and egraph
//  : SMTSolver        ( e, c )
  : SMTSolver        ( c, t )
  , axioms_checked   ( 0 )
  // Parameters: (formerly in 'SearchParams')
  , var_decay        ( 1 / 0.95 )
  , clause_decay     ( 1 / 0.999 )
  , random_var_freq  ( 0.02 )
  , learntsize_factor((double)1/(double)3)
  , learntsize_inc   ( 1.1 )
  // More parameters:
  //
  , expensive_ccmin  ( true )
  // Statistics: (formerly in 'SolverStats')
  //
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  // ADDED FOR MINIMIZATION
  , learnts_size(0) , all_learnts(0)
  , ok                    (true)
  , cla_inc               (1)
  , var_inc               (1)
  , qhead                 (0)
  , simpDB_assigns        (-1)
  , simpDB_props          (0)
  , order_heap            (VarOrderLt(activity))
  , random_seed           (c.getRandomSeed())
  , progress_estimate     (0)
  , remove_satisfied      (true)
  , learnt_t_lemmata      (0)
  , perm_learnt_t_lemmata (0)
  , luby_i                (0)
  , luby_k                (1)
  , cuvti                 (false)
#ifdef PRODUCE_PROOF
  , proof_                ( new Proof( ) )
  , proof                 ( * proof_ )
#endif
  , next_it_i             (0)
  , next_it_j             (1)
#ifdef STATISTICS
  , elim_tvars            (0)
#endif
  , init                  (false)
#ifdef PEDANTIC_DEBUG
  , max_dl_debug          (0)
  , analyze_cnt           (0)
#endif
{ }

void
CoreSMTSolver::initialize( )
{
  assert( config.isInit( ) );
//  assert( !init );
  random_seed = config.getRandomSeed();
  restart_first = config.sat_restart_first;
  restart_inc = config.sat_restart_inc;
  vec< Lit > fc;
  fc.push( lit_Undef );
  fake_clause = Clause_new( fc );
  // FIXME: check why this ?
  first_model_found = config.logic == QF_UFLRA
                   || config.logic == QF_UFIDL;
  // Set some parameters
  skip_step = config.sat_initial_skip_step;
  skipped_calls = 0;
#ifdef STATISTICS
  preproc_time = 0;
  tsolvers_time = 0;
  ie_generated = 0;
#endif
  //
  // Set polarity_mode
  //
  switch ( config.sat_polarity_mode )
  {
    case 0: polarity_mode = polarity_true;  break;
    case 1: polarity_mode = polarity_false; break;
    case 2: polarity_mode = polarity_rnd;   break;
    case 3: polarity_mode = polarity_user;  break; // Polarity is set in
    case 4: polarity_mode = polarity_user;  break; // THandler.C for
    case 5: polarity_mode = polarity_user;  break; // Boolean atoms
  }

  if ( config.logic == QF_AX
    || config.logic == QF_AXDIFF )
  {
    polarity_mode = polarity_false;
    // polarity_mode = polarity_true;
    // polarity_mode = polarity_rnd;
    opensmt_warning( "Overriding polarity for AX theory" );
  }

  init = true;
}

CoreSMTSolver::~CoreSMTSolver()
{
#ifdef PRODUCE_PROOF
  // Remove units
  for (int i = 0; i < units.size(); i++)
    if ( units[i] )
      proof.forceDelete( units[i] );
  for (int i = 0; i < tleaves.size(); i++) proof.forceDelete(tleaves[i]);
  for (int i = 0; i < pleaves.size(); i++) proof.forceDelete(pleaves[i]);
  for (int i = 0; i < learnts.size(); i++) proof.forceDelete(learnts[i]);
  for (int i = 0; i < clauses.size(); i++) proof.forceDelete(clauses[i]);
  for (int i = 0; i < axioms .size(); i++) proof.forceDelete(axioms [i]);
#else
  for (int i = 0; i < learnts.size(); i++) free(learnts[i]);
  for (int i = 0; i < clauses.size(); i++) free(clauses[i]);
  for (int i = 0; i < axioms .size(); i++) free(axioms [i]);
#endif

  for (int i = 0; i < tmp_reas.size(); i++) free(tmp_reas[i]);

#ifdef STATISTICS
  if ( config.produceStats() != 0 )
    printStatistics ( config.getStatsOut( ) );
  // TODO added for convenience
  if ( config.print_stats != 0 )
    printStatistics ( cerr );
#endif

//  delete theory_handler;
  free(fake_clause);
#ifdef PRODUCE_PROOF
  delete proof_;
#endif
}

//=================================================================================================
// Minor methods:

// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var CoreSMTSolver::newVar(bool sign, bool dvar)
{
  int v = nVars();
  watches   .push();          // (list for positive literal)
  watches   .push();          // (list for negative literal)
  reason    .push(NULL);
  assigns   .push(toInt(l_Undef));
  level     .push(-1);
#ifdef PRODUCE_PROOF
  trail_pos .push(-1);
#endif
  activity  .push(0);
  seen      .push(0);
#ifdef PRODUCE_PROOF
  units   .push( NULL );
#endif

  polarity    .push((char)sign);
  decision_var.push((char)dvar);

#if CACHE_POLARITY
  prev_polarity.push(toInt(l_Undef));
#endif

  insertVarOrder(v);

#ifndef SMTCOMP
  // Added Lines
  // Skip undo for varTrue and varFalse
  if ( v != 0 && v != 1 )
  {
    undo_stack_oper.push_back( NEWVAR );
    undo_stack_elem.push_back( reinterpret_cast< void * >( v ) );
  }
#endif

  n_occs.push(0);

  return v;
}

bool CoreSMTSolver::addClause( vec<Lit>& ps
#ifdef PRODUCE_PROOF
                             , ipartitions_t in
#endif
    )
{
  assert( decisionLevel() == 0 );
#ifdef PRODUCE_PROOF
  assert( in == 0 || ((in & (in - 1)) == 0) );
#endif

#ifdef PRODUCE_PROOF
  bool resolved = false;
  Clause * root = NULL;
#endif

  if (!ok)
    return false;
  else{
    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
#ifdef PRODUCE_PROOF
    root = Clause_new( ps, false );
    proof.addRoot( root, CLA_ORIG );
    assert( config.isInit( ) );
    if ( config.produce_inter > 0 )
      clause_to_partition[ root ] = in;
    proof.beginChain( root );
#endif
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
      if (value(ps[i]) == l_True || ps[i] == ~p)
      {
#ifdef PRODUCE_PROOF
        proof.endChain( );
        proof.forceDelete( root );
#endif
        // decrease the counts of those encountered so far
        for (int k = 0; k < j; k++) {
            n_occs[var(ps[k])] -= 1;
            assert(n_occs[var(ps[k])] >= 0);
        }
        return true;
      }
      else if (value(ps[i]) != l_False && ps[i] != p) {
        ps[j++] = p = ps[i];
        n_occs[var(ps[i])] += 1;
      }
#ifdef PRODUCE_PROOF
      else if ( value(ps[i]) == l_False )
      {
	resolved = true;
	proof.resolve( units[ var(ps[i]) ], var( ps[i] ) );
      }
#endif
    ps.shrink(i - j);
  }

  if (ps.size() == 0)
  {
#ifdef PRODUCE_PROOF
    proof.endChain( NULL );
    tleaves.push( root );
#endif
    return ok = false;
  }

#ifdef PRODUCE_PROOF
  Clause * res = NULL;
  if ( resolved )
  {
    res = Clause_new( ps, false );
    assert( res->size( ) < root->size( ) );
    proof.endChain( res );
    // Save root for removal
    tleaves.push( root );
  }
  else
  {
    res = root;
    // Throw away unnecessary chain
    proof.endChain( );
  }
#endif

  if (ps.size() == 1){
    assert(value(ps[0]) == l_Undef);
#ifdef PRODUCE_PROOF
    assert( res );
    assert( units[ var(ps[0]) ] == NULL );
    units[ var(ps[0]) ] = res;
    if ( config.produce_inter > 0
	&& var(ps[0]) > 1 ) // Avoids true/false
      units_to_partition.push_back( make_pair( res, in ) );
#endif
#ifdef PEDANTIC_DEBUG
    cout << toInt(ps[0]) << endl;
#endif
    uncheckedEnqueue(ps[0]);
#ifdef PRODUCE_PROOF
    Clause * confl = propagate();
    if ( confl == NULL ) return ok = true;
    return ok = false;
#else
    return ok = (propagate() == NULL);
#endif
  }else{

#ifdef PRODUCE_PROOF
    Clause * c = res;
#else
    Clause* c = Clause_new(ps, false);
#endif

#ifdef PRODUCE_PROOF
    if ( config.incremental )
    {
      undo_stack_oper.push_back( NEWPROOF );
      undo_stack_elem.push_back( (void *)c );
    }

    if ( config.produce_inter > 0 )
      clause_to_partition[ c ] = in;
#endif

    clauses.push(c);
    attachClause(*c);

#ifdef PEDANTIC_DEBUG
    for (int i = 0; i < c->size(); i++)
      cout << toInt((*c)[i]) << " ";
    cout << endl;
#endif

#ifndef SMTCOMP
    undo_stack_oper.push_back( NEWCLAUSE );
    undo_stack_elem.push_back( (void *)c );
#endif
  }


  return true;
}


void CoreSMTSolver::attachClause(Clause& c) {
  assert(c.size() > 1);
  watches[toInt(~c[0])].push(&c);
  watches[toInt(~c[1])].push(&c);
  if (c.learnt()) learnts_literals += c.size();
  else            clauses_literals += c.size();
}


void CoreSMTSolver::detachClause(Clause& c) {
  assert(c.size() > 1);
  assert(find(watches[toInt(~c[0])], &c));
  assert(find(watches[toInt(~c[1])], &c));
  remove(watches[toInt(~c[0])], &c);
  remove(watches[toInt(~c[1])], &c);
  if (c.learnt()) learnts_literals -= c.size();
  else            clauses_literals -= c.size();
}

void CoreSMTSolver::removeClause(Clause& c)
{
  assert( config.isInit( ) );
  if ( config.isIncremental() &&
      detached.find( &c ) != detached.end( ) )
  {
    detached.erase( &c );
  }
  else
    detachClause(c);
#ifdef PRODUCE_PROOF
  // Remove clause and derivations if ref becomes 0
  // If ref is not 0, we keep it and remove later
  if ( !proof.deleted( &c ) )
    pleaves.push( &c );
#else
  free(&c);
#endif
}

bool CoreSMTSolver::satisfied(const Clause& c) const
{
  for (int i = 0; i < c.size(); i++)
    if (value(c[i]) == l_True)
      return true;
  return false;
}


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void CoreSMTSolver::cancelUntil(int level)
{
  if (decisionLevel() > level)
  {
    int trail_lim_level = level == -1 ? 0 : trail_lim[ level ];

    for (int c = trail.size()-1; c >= trail_lim_level; c--)
    {
      Var     x  = var(trail[c]);
#ifdef PEDANTIC_DEBUG
      assert(assigns[x] != toInt(l_Undef));
#endif
      assigns[x] = toInt(l_Undef);
      insertVarOrder(x);
#ifdef PEDANTIC_DEBUG
      if (debug_reason_map.contains(x)) {
        checkTheoryReasonClause_debug(x);
        removeTheoryReasonClause_debug(x);
      }
#endif
    }
    qhead = trail_lim_level;
    trail.shrink(trail.size() - trail_lim_level);
    if ( level == -1 )
      trail_lim.shrink(0);
    else
      trail_lim.shrink(trail_lim.size() - level);

    // Changed this from decision level to trail.size()
    // the theory stack is in sync with the trail size, not the decision level!
    if ( first_model_found ) theory_handler.backtrack(trail.size());
  }
}

/*
void CoreSMTSolver::addSMTAxiomClause( vector< Enode * > & smt_clause
#ifdef PRODUCE_PROOF
                                     , Enode * interpolants
#endif
				     )
{
  assert( smt_clause.size( ) > 0 );

  vec< Lit > sat_clause;
  int nof_false = 0;
  Lit unass = lit_Undef;

  for ( vector< Enode * >::iterator it = smt_clause.begin( ) ;
      it != smt_clause.end( ) ;
      it ++ )
  {
    Enode * e = *it;

    if ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
      atoms_seen.insert( e );

    assert( !e->isTrue ( ) );
    assert( !e->isFalse( ) );

    Lit l = theory_handler->enodeToLit( e );

    // Shrink clause
    if ( value( l ) == l_False
      && level[ var(l) ] == 0 )
      continue;

    if ( value( l ) == l_False )
      nof_false ++;
    else if ( value( l ) != l_True )
      unass = l;

    sat_clause.push( l );

    // Can skip if satisfied at level 0 ...
    if ( value( l ) == l_True && level[ var(l) ] == 0 )
      return;
  }

  // assert( sat_clause.size( ) > 1 );
  Clause * ct = Clause_new( sat_clause );

  if ( config.incremental )
  {
    undo_stack_oper.push_back( NEWAXIOM );
    undo_stack_elem.push_back( (void *)ct );
  }

#ifdef PRODUCE_PROOF
  bool add_unit = false;
  proof.addRoot( ct, CLA_THEORY );
  if ( config.incremental )
  {
    undo_stack_oper.push_back( NEWPROOF );
    undo_stack_elem.push_back( (void *)ct );
  }
#endif

  // Boolean propagate if only one literal 
  // has survived. Others were all false
  // at decision level 0
  if ( sat_clause.size( ) == 1 )
  {
    uncheckedEnqueue( unass, ct );
#ifdef PRODUCE_PROOF
    units[ var( unass ) ] = ct;
    if ( config.produce_inter != 0 )
    {
      assert( interpolants );
      clause_to_in[ ct ] = interpolants;
    }
#endif
  }
  else
  {
    attachClause( *ct );
    axioms.push( ct );

    // Boolean propagate, but keep clause, 
    // if only one literal has survived at
    // this level
    if ( sat_clause.size( ) == nof_false + 1 
	&& unass != lit_Undef )
    {
      uncheckedEnqueue( unass, ct );
#ifdef PRODUCE_PROOF
      add_unit = true;
#endif
    }

    assert( config.isInit( ) );
#ifdef PRODUCE_PROOF
    // Assign clause for proof if unit propag occurred
    if ( add_unit )
      units[ var( unass ) ] = ct;

    if ( config.produce_inter != 0 )
    {
      assert( interpolants );
      clause_to_in[ ct ] = interpolants;
    }
#endif
  }
}
*/

/*
void CoreSMTSolver::addNewAtom( Enode * e )
{
  assert( e );
  assert( !e->isTrue ( ) );
  assert( !e->isFalse( ) );
  // Automatically adds new variable for e
  Lit l = theory_handler->enodeToLit( e );
}
*/

void CoreSMTSolver::cancelUntilVar( Var v )
{
  int c;
  for ( c = trail.size( )-1 ; var(trail[ c ]) != v ; c -- )
  {
    Var     x    = var(trail[ c ]);
    assigns[ x ] = toInt(l_Undef);
    insertVarOrder( x );
  }

  // Reset v itself
  assigns[ v ] = toInt(l_Undef);
  insertVarOrder( v );

  trail.shrink(trail.size( ) - c );
  qhead = trail.size( );

  if ( decisionLevel( ) > level[ v ] )
  {
    assert( c > 0 );
    assert( c - 1 < trail.size( ) );
    assert( var(trail[ c ]) == v );

    int lev = level[ var(trail[ c-1 ]) ];
    assert( lev < trail_lim.size( ) );

    trail_lim[ lev ] = c;
    trail_lim.shrink(trail_lim.size( ) - lev);
  }

  theory_handler.backtrack(trail.size());
}

void CoreSMTSolver::cancelUntilVarTempInit( Var v )
{
  assert( cuvti == false );
  cuvti = true;
  int c;
  for ( c = trail.size( )-1 ; var(trail[ c ]) != v ; c -- )
  {
    Lit p = trail[ c ];
    Var x = var( p );
    lit_to_restore.push( p );
    val_to_restore.push( assigns[ x ] );
    assigns[ x ] = toInt(l_Undef);
  }
  // Stores v as well
  Lit p = trail[ c ];
  Var x = var( p );
  assert( v == x );
  lit_to_restore.push( p );
  val_to_restore.push( assigns[ x ] );
  assigns[ x ] = toInt(l_Undef);

  // Reset v itself
  assigns[ v ] = toInt(l_Undef);

  trail.shrink(trail.size( ) - c );
  theory_handler.backtrack(trail.size());
}

void CoreSMTSolver::cancelUntilVarTempDone( )
{
  assert( cuvti == true );
  cuvti = false;

  while ( val_to_restore.size( ) > 0 )
  {
    Lit p = lit_to_restore.last( );
    Var x = var( p );
    lit_to_restore.pop( );
    char v = val_to_restore.last( );
    val_to_restore.pop( );
    assigns[ x ] = v;
    trail.push( p );
  }

  const bool res = theory_handler.assertLits(trail);
#ifdef PEDANTIC_DEBUG
  theory_handler.checkTrailConsistency(trail);
#endif
  // Flush conflict if unsat
  if ( !res )
  {
//    assert(false);
    vec< Lit > conflicting;
    int        max_decision_level;
#ifdef PEDANTIC_DEBUG
    theory_handler.getConflict( conflicting, level, max_decision_level, assigns, trail );
#else
    theory_handler.getConflict( conflicting, level, max_decision_level, assigns );
#endif
  }
}

//=================================================================================================
// Major methods:

Lit CoreSMTSolver::pickBranchLit(int polarity_mode, double random_var_freq)
{
  Var next = var_Undef;

  // Random decision:
  if (drand(random_seed) < random_var_freq && !order_heap.empty()){
    next = order_heap[irand(random_seed,order_heap.size())];
    if (toLbool(assigns[next]) == l_Undef && decision_var[next])
      rnd_decisions++; }

    // Theory suggestion-based decision
    for( ;; )
    {
      Lit sugg = lit_Undef; //= theory_handler->getSuggestion( );
      // No suggestions
      if ( sugg == lit_Undef )
	break;
      // Atom already assigned or not to be used as decision
      if ( toLbool(assigns[var(sugg)]) != l_Undef || !decision_var[var(sugg)] )
	continue;
      // If here, good decision has been found
      return sugg;
    }

    // Activity based decision:
    while (next == var_Undef || toLbool(assigns[next]) != l_Undef || !decision_var[next])
      if (order_heap.empty()){
	next = var_Undef;
	break;
      }else
	next = order_heap.removeMin();

      if ( next == var_Undef
	  && ( config.logic == QF_UFIDL || config.logic == QF_UFLRA )
	  && config.sat_lazy_dtc != 0 )
      {
//	next = generateMoreEij( );

	/*
	if ( next != var_Undef )
	  cerr << "Generated eij " << next << ", with value " << ( value( next ) == l_True 
	      ? "T" 
	      : value( next ) == l_False
	      ? "F"
	      : "U" ) << endl;
	*/
      }


      if ( next == var_Undef )
	return lit_Undef;

#if CACHE_POLARITY
      if ( prev_polarity[ next ] != toInt(l_Undef) )
	return Lit( next, prev_polarity[ next ] < 0 );
#endif

      bool sign = false;
      switch ( polarity_mode )
      {
	case polarity_true:  sign = false; break;
	case polarity_false: sign = true;  break;
	case polarity_user:  sign = polarity[next]; break;
	case polarity_rnd:   sign = irand(random_seed, 2); break;
	default: assert(false); 
      }

      return next == var_Undef ? lit_Undef : Lit(next, sign);
}

#ifdef PRODUCE_PROOF
class lastToFirst_lt {  // Helper class to 'analyze' -- order literals from last to first occurance in 'trail[]'.
  const vec<int>& trail_pos;
  public:
  lastToFirst_lt(const vec<int>& t) : trail_pos(t) {}
  bool operator () (Lit p, Lit q) { return trail_pos[var(p)] > trail_pos[var(q)]; }
};
#endif

/*_________________________________________________________________________________________________
  |
  |  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
  |
  |  Description:
  |    Analyze conflict and produce a reason clause.
  |
  |    Pre-conditions:
  |      * 'out_learnt' is assumed to be cleared.
  |      * Current decision level must be greater than root level.
  |
  |    Post-conditions:
  |      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
  |
  |  Effect:
  |    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
  |________________________________________________________________________________________________@*/

void CoreSMTSolver::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel)
{
#ifdef PEDANTIC_DEBUG
  cerr << "analyze " << analyze_cnt++ << endl;
#endif
#ifdef PRODUCE_PROOF
  assert( proof.checkState( ) );
#endif

  assert( confl );
  assert( cleanup.size( ) == 0 );       // Cleanup stack must be empty

  int pathC = 0;
  Lit p     = lit_Undef;

  // Generate conflict clause:
  //
  out_learnt.push();      // (leave room for the asserting literal)
  int index   = trail.size() - 1;
  out_btlevel = 0;

#ifdef PRODUCE_PROOF
  proof.beginChain( confl );
#endif

  do{
    assert(confl != NULL);          // (otherwise should be UIP)
    Clause& confl_curr = *confl;

    if (confl_curr.learnt())
      claBumpActivity(confl_curr);

    for (int j = (p == lit_Undef) ? 0 : 1; j < confl_curr.size(); j++)
    {
      Lit q = confl_curr[j];

      if (!seen[var(q)] && level[var(q)] > 0){

	varBumpActivity(var(q));
	seen[var(q)] = 1;
	// Variable propagated at current level
	if (level[var(q)] >= decisionLevel())
	  // Increment counter for number of pivot variables left on which to resolve
	  pathC++;
	else{
	  // Variable propagated at previous level
	  out_learnt.push(q);
	  // Keep track of highest among levels except current one
	  if (level[var(q)] > out_btlevel)
	    out_btlevel = level[var(q)];
	}
      }
#ifdef PRODUCE_PROOF
      else if( !seen[var(q)] )
      {
	if ( level[ var(q) ] == 0 )
	{
	  proof.resolve( units[ var( q ) ], var( q ) );
	}
      }
#endif
    }

    // Select next clause to look at:
    while (!seen[var(trail[index--])])
      ; // Do nothing
    p     = trail[index+1];

    if ( reason[var(p)] != NULL && reason[var(p)] == fake_clause )
    {
      // Before retrieving the reason it is necessary to backtrack
      // a little bit in order to remove every atom pushed after
      // p has been deduced
      Var v = var(p);
      assert(value(p) == l_True);
      // Backtracking the trail until v is the variable on the top
      cancelUntilVarTempInit( v );

      vec< Lit > r;
      // Retrieving the reason
#ifdef STATISTICS
      const double start = cpuTime( );
#endif
#ifdef PEDANTIC_DEBUG
      if (theory_handler.getReason( p, r, assigns ) == false) {
        assert(debug_reason_map.contains(var(p)));
        int idx = debug_reason_map[var(p)];
        Clause* c = debug_reasons[idx];
        cerr << "Could not find reason " << theory_handler.printAsrtClause(c) << endl;
        assert(false);
      }
#else
      theory_handler.getReason( p, r, assigns );
#endif
      assert(r.size() > 0);
      cancelUntilVarTempDone();
#ifdef STATISTICS
      tsolvers_time += cpuTime( ) - start;
#endif

      Clause * ct = NULL;
      if ( r.size( ) > config.sat_learn_up_to_size )
      {
	ct = Clause_new( r );
	cleanup.push( ct );
      }
      else
      {
	bool learnt_ = config.sat_temporary_learn;
	ct = Clause_new( r, learnt_ );
	learnts.push(ct);
#ifndef SMTCOMP
	undo_stack_oper.push_back( NEWLEARNT );
	undo_stack_elem.push_back( (void *)ct );
#endif
	attachClause(*ct);
	claBumpActivity(*ct);
	learnt_t_lemmata ++;
	if ( !config.sat_temporary_learn )
	  perm_learnt_t_lemmata ++;
      }
      assert( ct );
      reason[var(p)] = ct;
#ifdef PRODUCE_PROOF
      proof.addRoot( ct, CLA_THEORY );
      if ( config.incremental )
      {
	undo_stack_oper.push_back( NEWPROOF );
	undo_stack_elem.push_back( (void *)ct );
      }
      if ( config.produce_inter > 0 )
      {
//	Enode * interpolants = theory_handler->getInterpolants( );
//	assert( interpolants );
//	clause_to_in[ ct ] = interpolants;
	if ( config.incremental )
	{
	  undo_stack_oper.push_back( NEWINTER );
	  undo_stack_elem.push_back( NULL );
	}
      }
#endif
    }

    confl = reason[var(p)]; // NB: this could be a cleanup clause

    // RB: If this assertion fails, most of the times
    // it is because you have recently propagated something
    // that should have been propagated before the current
    // decision level. This is possible in SMT as we add
    // new clauses like crazy in a different way as the
    // SAT solver normally does. Here an example of failure.
    // We have the trail
    //  1:0
    // -2:0
    //  ...
    //  7:2
    //  where 7 is the last decision variable, and now
    //  we add the clause ( 8 2 ), which would propagate 8
    //  ...
    //  7:2
    //  8:2
    //  however the appropriate propagation level for
    //  8 is 0. You should always backtrack to the appropriate
    //  level before doing propagations
    assert( pathC == 1 || confl != NULL );

    seen[var(p)] = 0;
    pathC--;

#ifdef PRODUCE_PROOF
    if ( pathC > 0 )
    {
      proof.resolve( confl, var( p ) );
    }
#endif

  } while (pathC > 0);

  assert(p != lit_Undef);
  assert((~p) != lit_Undef);
  // Current level UIP
  out_learnt[0] = ~p;

  // Simplify conflict clause:
  //
  int i, j;
  if (expensive_ccmin) {
    uint32_t abstract_level = 0;
    for (i = 1; i < out_learnt.size(); i++)
      abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

#ifdef PRODUCE_PROOF
    analyze_proof.clear( );
#endif
    out_learnt.copyTo(analyze_toclear);

    for (i = j = 1; i < out_learnt.size(); i++)
      if (reason[var(out_learnt[i])] == NULL || !litRedundant(out_learnt[i], abstract_level))
	out_learnt[j++] = out_learnt[i];
  } else {
    // Added line
    assert( false );
    out_learnt.copyTo(analyze_toclear);
    for (i = j = 1; i < out_learnt.size(); i++){
      Clause& c = *reason[var(out_learnt[i])];
      for (int k = 1; k < c.size(); k++)
	if (!seen[var(c[k])] && level[var(c[k])] > 0){
	  out_learnt[j++] = out_learnt[i];
	  break; }
    }
  }
  max_literals += out_learnt.size();
  out_learnt.shrink(i - j);
  tot_literals += out_learnt.size();

  // Find correct backtrack level:
  //
  if (out_learnt.size() == 1)
    out_btlevel = 0;
  else {
    int max_i = 1;
    for (int i = 2; i < out_learnt.size(); i++)
      if (level[var(out_learnt[i])] > level[var(out_learnt[max_i])])
        max_i = i;

    Lit p             = out_learnt[max_i];
    out_learnt[max_i] = out_learnt[1];
    out_learnt[1]     = p;
    out_btlevel       = level[var(p)];
  }

#ifdef PRODUCE_PROOF
  // Finalize proof logging with conflict clause minimization steps:
  //
  sort( analyze_proof, lastToFirst_lt(trail_pos) );
  for ( int k = 0 ; k < analyze_proof.size() ; k++ )
  {
    Var v = var( analyze_proof[ k ] ); assert( level[ v ] > 0 );
    // Skip decision variables
    // if ( reason[ v ] == NULL ) continue;
    assert( reason[ v ] );
    Clause & c = *reason[ v ];
    proof.resolve( &c, v );
    for ( int j = 0 ; j < c.size( ) ; j++ )
      if ( level[ var(c[j]) ] == 0 )
      {
	proof.resolve( units[ var(c[j]) ], var(c[j]) );
      }
  }
  // Chain will be ended outside analyze
#endif

  for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

  // Cleanup generated lemmata
  for ( int i = 0 ; i < cleanup.size() ; i ++ )
#ifdef PRODUCE_PROOF
  {
    // Theory lemma automatically cleaned
    tleaves.push( cleanup[ i ] );
#endif

#ifdef PRODUCE_PROOF
#else
    {
      free(cleanup[ i ]);
    }
#endif

#ifdef PRODUCE_PROOF
  }
#endif
  cleanup.clear();
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool CoreSMTSolver::litRedundant(Lit p, uint32_t abstract_levels)
{
#ifdef PRODUCE_PROOF
  // Dunno how to handle this case in proof !
  return false;
#endif

  if ( config.sat_minimize_conflicts <= 0 )
    return false;

  analyze_stack.clear(); analyze_stack.push(p);
  int top = analyze_toclear.size();
  while (analyze_stack.size() > 0){
    assert(reason[var(analyze_stack.last())] != NULL);

    if( config.sat_minimize_conflicts >= 2 )
    {
      if ( reason[ var(analyze_stack.last()) ] == fake_clause )
      {
	// Before retrieving the reason it is necessary to backtrack
	// a little bit in order to remove every atom pushed after
	// p has been deduced
	Lit p = analyze_stack.last( );
	Var v = var( p );
	vec< Lit > r;
	// Temporairly backtracking
	cancelUntilVarTempInit( v );
	// Retrieving the reason
#ifdef PEDANTIC_DEBUG
	if (theory_handler.getReason( p, r, assigns ) == false) {
            assert(debug_reason_map.contains(var(p)));
            int idx = debug_reason_map[var(p)];
            Clause* c = debug_reasons[idx];
            cerr << theory_handler.printAsrtClause(c) << endl;
            assert(false);
        }
#else
	theory_handler.getReason( p, r, assigns );
#endif
	// Restoring trail
	cancelUntilVarTempDone( );
	Clause * ct = NULL;
	if ( r.size( ) > config.sat_learn_up_to_size )
	{
	  ct = Clause_new( r );
	  tmp_reas.push( ct );
	}
	else
	{
	  ct = Clause_new( r, config.sat_temporary_learn );
	  learnts.push(ct);
#ifndef SMTCOMP
	  if ( config.isIncremental() != 0 )
	  {
	    undo_stack_oper.push_back( NEWLEARNT );
	    undo_stack_elem.push_back( (void *)ct );
	  }
#endif
	  attachClause(*ct);
	  claBumpActivity(*ct);
	  learnt_t_lemmata ++;
	  if ( !config.sat_temporary_learn )
	    perm_learnt_t_lemmata ++;
	}
	reason[ v ] = ct;
#ifdef PRODUCE_PROOF
	proof.addRoot( ct, CLA_THEORY );
	if ( config.incremental )
	{
	  undo_stack_oper.push_back( NEWPROOF );
	  undo_stack_elem.push_back( (void *)ct );
	}
	if ( config.produce_inter > 0 )
	{
	  Enode * interpolants = theory_handler->getInterpolants( );
	  assert( interpolants );
	  clause_to_in[ ct ] = interpolants;
	  if ( config.incremental )
	  {
	    undo_stack_oper.push_back( NEWINTER );
	    undo_stack_elem.push_back( NULL );
	  }
	}
#endif
      }
    }
    else
    {
      assert( config.sat_minimize_conflicts == 1 );
      // Just give up when fake reason is found -- but clean analyze_toclear
      if( reason[ var(analyze_stack.last()) ] == fake_clause )
      {
	for (int j = top; j < analyze_toclear.size(); j++)
	  seen[var(analyze_toclear[j])] = 0;
	analyze_toclear.shrink(analyze_toclear.size() - top);

	return false;
      }
    }

    Clause& c = *reason[var(analyze_stack.last())];

    analyze_stack.pop();

    for (int i = 1; i < c.size(); i++){
      Lit p  = c[i];

      if (!seen[var(p)] && level[var(p)] > 0){

	if (reason[var(p)] != NULL && (abstractLevel(var(p)) & abstract_levels) != 0){
	  seen[var(p)] = 1;
	  analyze_stack.push(p);
	  analyze_toclear.push(p);
	}else{
	  for (int j = top; j < analyze_toclear.size(); j++)
	    seen[var(analyze_toclear[j])] = 0;
	  analyze_toclear.shrink(analyze_toclear.size() - top);

	  return false;
	}
      }
    }
  }

#ifdef PRODUCE_PROOF
  analyze_proof.push( p );
#endif

  return true;
}

/*_________________________________________________________________________________________________
  |
  |  analyzeFinal : (p : Lit)  ->  [void]
  |
  |  Description:
  |    Specialized analysis procedure to express the final conflict in terms of assumptions.
  |    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
  |    stores the result in 'out_conflict'.
  |________________________________________________________________________________________________@*/
void CoreSMTSolver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
#ifdef PRODUCE_PROOF
  opensmt_error( "case not handled (yet)" );
#endif
  out_conflict.clear();
  out_conflict.push(p);

  if (decisionLevel() == 0)
    return;

  seen[var(p)] = 1;

  for (int i = trail.size()-1; i >= trail_lim[0]; i--){
    Var x = var(trail[i]);
    if (seen[x]){
      if (reason[x] == NULL){
	assert(level[x] > 0);
	out_conflict.push(~trail[i]);
      }else{
	Clause& c = *reason[x];
	for (int j = 1; j < c.size(); j++)
	  if (level[var(c[j])] > 0)
	    seen[var(c[j])] = 1;
      }
      seen[x] = 0;
    }
  }

  seen[var(p)] = 0;
}


void CoreSMTSolver::uncheckedEnqueue(Lit p, Clause* from)
{
#ifdef PEDANTIC_DEBUG
  assert(from == fake_clause || !debug_reason_map.contains(var(p)));
#endif
  assert(value(p) == l_Undef);
  assigns [var(p)] = toInt(lbool(!sign(p)));  // <<== abstract but not uttermost effecient

  level   [var(p)] = decisionLevel();
  reason  [var(p)] = from;

  // Added Code
#if CACHE_POLARITY
  prev_polarity[var(p)] = assigns[var(p)];
#endif

  trail.push(p);

#ifdef PRODUCE_PROOF
  trail_pos[var(p)] = trail.size();
#endif
}


/*_________________________________________________________________________________________________
  |
  |  propagate : [void]  ->  [Clause*]
  |
  |  Description:
  |    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
  |    otherwise NULL.
  |
  |    Post-conditions:
  |      * the propagation queue is empty, even if there was a conflict.
  |________________________________________________________________________________________________@*/
Clause* CoreSMTSolver::propagate()
{
  Clause* confl     = NULL;
  int     num_props = 0;

  while (qhead < trail.size()){
    Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.

    vec<Clause*>&  ws  = watches[toInt(p)];
    Clause         **i, **j, **end;
    num_props++;

    for (i = j = (Clause**)ws, end = i + ws.size();  i != end;){
      Clause& c = **i++;

      // Make sure the false literal is data[1]:
      Lit false_lit = ~p;
      if (c[0] == false_lit)
        c[0] = c[1], c[1] = false_lit;

      assert(c[1] == false_lit);

      // If 0th watch is true, then clause is already satisfied.
      Lit first = c[0];
      if (value(first) == l_True){
	*j++ = &c;
      }else{
	// Look for new watch:
	for (int k = 2; k < c.size(); k++)
	  if (value(c[k]) != l_False){
	    c[1] = c[k]; c[k] = false_lit;
	    watches[toInt(~c[1])].push(&c);
	    goto FoundWatch; }

#ifdef PRODUCE_PROOF
	    // Did not find watch -- clause is unit under assignment:
	    if ( decisionLevel() == 0 )
	    {
	      proof.beginChain( &c );
	      for (int k = 1; k < c.size(); k++)
	      {
		assert( level[ var(c[k]) ] == 0 );
		proof.resolve( units[var(c[k])], var(c[k]) );
	      }
	      assert( units[ var(first) ] == NULL
		  || value( first ) == l_False );    // (if variable already has 'id', it must be with the other polarity and we should have derived the empty clause here)
	      if ( value(first) != l_False )
	      {
		vec< Lit > tmp;
		tmp.push( first );
		Clause * uc = Clause_new( tmp );
		proof.endChain( uc );
		assert( units[ var(first) ] == NULL );
		units[ var(first) ] = uc;
	      }
	      else
	      {
		vec< Lit > tmp;
		tmp.push( first );
		Clause * uc = Clause_new( tmp );
		proof.endChain( uc );
		pleaves.push( uc );
		// Empty clause derived:
		proof.beginChain( units[ var(first) ] );
		proof.resolve( uc, var(first) );
		proof.endChain( NULL );
	      }
	    }
#endif

	    // Did not find watch -- clause is unit under assignment:
	    *j++ = &c;
	    if (value(first) == l_False){
	      confl = &c;
	      qhead = trail.size();
	      // Copy the remaining watches:
	      while (i < end)
		*j++ = *i++;
	    }else
	      uncheckedEnqueue(first, &c);
      }
FoundWatch:;
    }
    ws.shrink(i - j);
  }
  propagations += num_props;
  simpDB_props -= num_props;

  return confl;
}

/*_________________________________________________________________________________________________
  |
  |  reduceDB : ()  ->  [void]
  |
  |  Description:
  |    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
  |    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
  |________________________________________________________________________________________________@*/
struct reduceDB_lt { bool operator () (Clause* x, Clause* y) { return x->size() > 2 && (y->size() == 2 || x->activity() < y->activity()); } };
void CoreSMTSolver::reduceDB()
{
  int     i, j;
  double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

  sort(learnts, reduceDB_lt());
  for (i = j = 0; i < learnts.size() / 2; i++){
    if (learnts[i]->size() > 2 && !locked(*learnts[i]))
      removeClause(*learnts[i]);
    else
      learnts[j++] = learnts[i];
  }
  for (; i < learnts.size(); i++){
    if (learnts[i]->size() > 2 && !locked(*learnts[i]) && learnts[i]->activity() < extra_lim)
      removeClause(*learnts[i]);
    else
      learnts[j++] = learnts[i];
  }
  learnts.shrink(i - j);

#ifdef PRODUCE_PROOF
  // Remove unused theory lemmata
  for ( i = j = 0 ; i < tleaves.size( ) ; i++ )
  {
    /* RB: Not clear if it is safe, probably not
    // Remove if satisfied at dec level 0
    if (decisionLevel( ) == 0 && satisfied( *tleaves[i] ))
    proof.forceDelete( tleaves[i], true );
    else
    */
    if ( proof.deleted( tleaves[i] ) )
      ; // Do nothing
    else
      tleaves[j++] = tleaves[i];
  }
  tleaves.shrink(i - j);
  // Remove unused leaves
  for ( i = j = 0 ; i < pleaves.size( ) ; i++ )
  {
    /* RB: Not clear if it is safe, probably not
    // Remove if satisfied at dec level 0
    if (decisionLevel( ) == 0 && satisfied( *pleaves[i] ))
    proof.forceDelete( pleaves[i], true );
    else
    */
    if ( proof.deleted( pleaves[i] ) )
      ; // Do nothing
    else
      pleaves[j++] = pleaves[i];
  }
  pleaves.shrink(i - j);
#endif
}

void CoreSMTSolver::removeSatisfied(vec<Clause*>& cs)
{
  int i,j;
  for (i = j = 0; i < cs.size(); i++){
    if (satisfied(*cs[i]))
      removeClause(*cs[i]);
    else
      cs[j++] = cs[i];
  }
  cs.shrink(i - j);
}


/*_________________________________________________________________________________________________
  |
  |  simplify : [void]  ->  [bool]
  |
  |  Description:
  |    Simplify the clause database according to the current top-level assigment. Currently, the only
  |    thing done here is the removal of satisfied clauses, but more things can be put here.
  |________________________________________________________________________________________________@*/
bool CoreSMTSolver::simplify()
{
  assert(decisionLevel() == 0);

  if (!ok || propagate() != NULL)
    return ok = false;

  if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
    return true;

  // Remove satisfied clauses:
  removeSatisfied(learnts);
  // removeSatisfied(axioms);
  if (remove_satisfied)        // Can be turned off.
    removeSatisfied(clauses);

  // Remove fixed variables from the variable heap:
  order_heap.filter(VarFilter(*this));

  simpDB_assigns = nAssigns();
  simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

  return true;
}

  void
CoreSMTSolver::pushBacktrackPoint( )
{
  assert( config.isIncremental() );
  //
  // Save undo stack size
  //
  assert( undo_stack_oper.size( ) == undo_stack_elem.size( ) );
  undo_stack_size.push_back( undo_stack_oper.size( ) );
  undo_trail_size.push_back( trail.size( ) );
#ifdef PRODUCE_PROOF
  proof.pushBacktrackPoint( );
#endif
}

void CoreSMTSolver::popBacktrackPoint ( )
{
  assert( config.isIncremental() );
  //
  // Force restart, but retain assumptions
  //
  cancelUntil(0);
  //
  // Shrink back trail
  //
  int new_trail_size = undo_trail_size.back( );
  undo_trail_size.pop_back( );
  for ( int i = trail.size( ) - 1 ; i >= new_trail_size ; i -- )
  {
    Var     x  = var(trail[i]);
    assigns[x] = toInt(l_Undef);
    reason [x] = NULL;
    insertVarOrder(x);
  }
  trail.shrink(trail.size( ) - new_trail_size);
  assert( trail_lim.size( ) == 0 );
  qhead = trail.size( );
  //
  // Undo operations
  //
  size_t new_stack_size = undo_stack_size.back( );
  undo_stack_size.pop_back( );
  while ( undo_stack_oper.size( ) > new_stack_size )
  {
    const oper_t op = undo_stack_oper.back( );

    if ( op == NEWVAR )
    {
#ifdef BUILD_64
      long xl = reinterpret_cast< long >( undo_stack_elem.back( ) );
      const Var x = static_cast< Var >( xl );
#else
      const Var x = reinterpret_cast< int >( undo_stack_elem.back( ) );
#endif

      // Undoes insertVarOrder( )
      assert( order_heap.inHeap(x) );
      order_heap  .remove(x);
      // Undoes decision_var ... watches
      decision_var.pop();
      polarity    .pop();
      seen        .pop();
      activity    .pop();
      level       .pop();
      assigns     .pop();
      reason      .pop();
      watches     .pop();
      watches     .pop();
      // Remove variable from translation tables
//      theory_handler->clearVar( x );
    }
    else if ( op == NEWUNIT )
      ; // Do nothing
    else if ( op == NEWCLAUSE )
    {
      Clause * c = (Clause *)undo_stack_elem.back( );
      assert( clauses.last( ) == c );
      clauses.pop( );
      removeClause( *c );
    }
    else if ( op == NEWLEARNT )
    {
      Clause * c = (Clause *)undo_stack_elem.back( );
      detachClause( *c );
      detached.insert( c );
    }
    else if ( op == NEWAXIOM )
    {
      Clause * c = (Clause *)undo_stack_elem.back( );
      assert( axioms.last( ) == c );
      axioms.pop( );
      removeClause( *c );
    }
#ifdef PRODUCE_PROOF
    else if ( op == NEWPROOF )
    {
      assert( false );
    }
    else if ( op == NEWINTER )
      ; // Do nothing. Ids are never reset ...
#endif
    else
    {
      opensmt_error2( "unknown undo operation in CoreSMTSolver", op );
    }

    undo_stack_oper.pop_back( );
    undo_stack_elem.pop_back( );
  }

  assert( undo_stack_elem.size( ) == undo_stack_oper.size( ) );
#ifdef PRODUCE_PROOF
  proof.popBacktrackPoint( );
#endif
  // Backtrack theory solvers
  theory_handler.backtrack(trail.size());
  // Restore OK
  restoreOK( );
  assert( isOK( ) );
}

void CoreSMTSolver::reset( )
{
  assert( config.isIncremental() );
  //
  // Force restart, but retain assumptions
  //
  cancelUntil(0);
  //
  // Shrink back trail
  //
  undo_trail_size.clear( );
  int new_trail_size = 0;
  for ( int i = trail.size( ) - 1 ; i >= new_trail_size ; i -- )
  {
    Var     x  = var(trail[i]);
    assigns[x] = toInt(l_Undef);
    reason [x] = NULL;
    insertVarOrder(x);
  }
  trail.shrink(trail.size( ) - new_trail_size);
  assert( trail_lim.size( ) == 0 );
  qhead = trail.size( );
  //
  // Undo operations
  //
  while ( undo_stack_oper.size( ) > 0 )
  {
    const oper_t op = undo_stack_oper.back( );

    if ( op == NEWVAR )
    {
#ifdef BUILD_64
      long xl = reinterpret_cast< long >( undo_stack_elem.back( ) );
      const Var x = static_cast< Var >( xl );
#else
      const Var x = reinterpret_cast< int >( undo_stack_elem.back( ) );
#endif

      // Undoes insertVarOrder( )
      assert( order_heap.inHeap(x) );
      order_heap  .remove(x);
      // Undoes decision_var ... watches
      decision_var.pop();
      polarity    .pop();
      seen        .pop();
      activity    .pop();
      level       .pop();
      assigns     .pop();
      reason      .pop();
      watches     .pop();
      watches     .pop();
      // Remove variable from translation tables
//      theory_handler->clearVar( x );
    }
    else if ( op == NEWUNIT )
      ; // Do nothing
    else if ( op == NEWCLAUSE )
    {
      Clause * c = (Clause *)undo_stack_elem.back( );
      assert( clauses.last( ) == c );
      clauses.pop( );
      removeClause( *c );
    }
    else if ( op == NEWLEARNT )
    {
      Clause * c = (Clause *)undo_stack_elem.back( );
      removeClause( *c );
    }
    else if ( op == NEWAXIOM )
    {
      Clause * c = (Clause *)undo_stack_elem.back( );
      assert( axioms.last( ) == c );
      axioms.pop( );
      removeClause( *c );
    }
#ifdef PRODUCE_PROOF
    else if ( op == NEWPROOF )
    {
      assert( false );
    }
    else if ( op == NEWINTER )
      ; // Do nothing
#endif
    else
    {
      opensmt_error2( "unknown undo operation in CoreSMTSolver", op );
    }

    undo_stack_oper.pop_back( );
    undo_stack_elem.pop_back( );
  }
  //
  // Clear all learnts
  //
  while( learnts.size( ) > 0 )
  {
    Clause * c = learnts.last( );
    learnts.pop( );
    removeClause( *c );
  }
#ifdef PRODUCE_PROOF
  proof.reset( );
#endif
  assert( undo_stack_elem.size( ) == undo_stack_oper.size( ) );
  assert( learnts.size( ) == 0 );
}


/*_________________________________________________________________________________________________
  |
  |  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
  |
  |  Description:
  |    Search for a model the specified number of conflicts, keeping the number of learnt clauses
  |    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
  |    indicate infinity.
  |
  |  Output:
  |    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
  |    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
  |    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
  |________________________________________________________________________________________________@*/
lbool CoreSMTSolver::search(int nof_conflicts, int nof_learnts)
{
#ifdef PRODUCE_PROOF
  // Force disable theory propagation, since we don't
  // have at the moment we don't construct the reasons
  // for the propagated literals
  config.sat_theory_propagation = 0;
#endif
  assert(ok);
  int         backtrack_level;
  int         conflictC = 0;
  vec<Lit>    learnt_clause;

  starts++;

  bool first = true;

#ifdef STATISTICS
  const double start = cpuTime( );
#endif
  // (Incomplete) Check of Level-0 atoms

  int res = checkTheory( false );
  if ( res == -1 ) return l_False;
  while ( res == 2 )
    res = checkTheory( false );
  assert( res == 1 );
#ifdef STATISTICS
  tsolvers_time += cpuTime( ) - start;
#endif

  //
  // Decrease activity for booleans
  //
  boolVarDecActivity( );

#ifdef PEDANTIC_DEBUG
  bool thr_backtrack = false;
#endif
  for (;;)
  {
    // Added line
    if ( opensmt::stop ) return l_Undef;

    Clause* confl = propagate();
    if (confl != NULL){
#ifdef PEDANTIC_DEBUG
      if (thr_backtrack == true)
        cerr << "Bling! Theory backtrack resulted in conflict" << endl;
#endif
      // CONFLICT
      conflicts++; conflictC++;
      if (decisionLevel() == 0)
        return l_False;

      first = false;
      learnt_clause.clear();
      analyze(confl, learnt_clause, backtrack_level);

#ifdef PEDANTIC_DEBUG
      cerr << "Backtracking due to SAT conflict "
           << decisionLevel() - backtrack_level << endl;
      int init_trail_sz = trail.size();
#endif

      cancelUntil(backtrack_level);
#ifdef PEDANTIC_DEBUG
      cerr << "Backtracking due to SAT conflict done" << endl;
      cerr << "Backtracked " << init_trail_sz - trail.size()
           << " variables." << endl;
#endif
      assert(value(learnt_clause[0]) == l_Undef);

      if (learnt_clause.size() == 1){
        uncheckedEnqueue(learnt_clause[0]);
#ifdef PRODUCE_PROOF
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

    }else{
      // NO CONFLICT
#ifdef PEDANTIC_DEBUG
      if (thr_backtrack)
        cerr << "Bling! No theory backtracking" << endl;
    thr_backtrack = false;
#endif
      if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
        // Reached bound on number of conflicts:
        progress_estimate = progressEstimate();
        cancelUntil(0);
        return l_Undef; }

        // Simplify the set of problem clauses:
        if (decisionLevel() == 0 && !simplify())
          return l_False;

        if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
          // Reduce the set of learnt clauses:
          reduceDB();

        if ( first_model_found )
        {
          // Early Pruning Call
          // Step 1: check if the current assignment is theory-consistent
#ifdef STATISTICS
          const double start = cpuTime( );
#endif
#ifdef PEDANTIC_DEBUG
          int prev_dl = decisionLevel();
#endif
          int res = checkTheory( false );
#ifdef STATISTICS
          tsolvers_time += cpuTime( ) - start;
#endif
          switch( res )
          {
            case -1: return l_False;        // Top-Level conflict: unsat
            case  0: conflictC++; continue; // Theory conflict: time for bcp
            case  1: break;                 // Sat and no deductions: go ahead
            case  2:                        // Sat and deductions: time for bcp
#ifdef PEDANTIC_DEBUG
              thr_backtrack = (decisionLevel() != prev_dl);
#endif
              continue;
            default: assert( false );
          }

          // Check axioms
//          res = checkAxioms( );
//
//          switch( res )
//          {
//            case -1: return l_False;        // Top-Level conflict: unsat
//            case  0: conflictC++; continue; // Theory conflict: time for bcp
//            case  1: break;                 // Sat and no deductions: go ahead
//            case  2: continue;              // Sat and deductions: time for bcp
//            default: assert( false );
//          }
        }

        Lit next = lit_Undef;
        while (decisionLevel() < assumptions.size()){
          // Perform user provided assumption:
          Lit p = assumptions[decisionLevel()];
          if (value(p) == l_True){
            // Dummy decision level:
            newDecisionLevel();
          }else if (value(p) == l_False){
            analyzeFinal(~p, conflict);
            return l_False;
          }else{
            next = p;
            break;
          }
        }

        if (next == lit_Undef)
        {
          // New variable decision:
          decisions++;
          next = pickBranchLit(polarity_mode, random_var_freq);
#ifdef PEDANTIC_DEBUG
          cout << "branch: " << toInt(next) << endl;
#endif
          // Complete Call
          if ( next == lit_Undef )
          {
            first_model_found = true;
#ifdef STATISTICS
            const double start = cpuTime( );
#endif
            int res = checkTheory( true );
#ifdef STATISTICS
            tsolvers_time += cpuTime( ) - start;
#endif
            if ( res == 0 ) { conflictC++; continue; }
            if ( res == -1 ) return l_False;
            assert( res == 1 );

#ifdef STATISTICS
            const double start2 = cpuTime( );
#endif
//	    res = checkAxioms( );
#ifdef STATISTICS
            tsolvers_time += cpuTime( ) - start2;
#endif

//            if ( res == 0 ) { conflictC++; continue; }
//            if ( res == 2 ) { continue; }
//            if ( res == -1 ) return l_False;
//            assert( res == 1 );
            // Otherwise we still have to make sure that
            // splitting on demand did not add any new variable
            decisions++;
            next = pickBranchLit( polarity_mode, random_var_freq );
          }

          if (next == lit_Undef)
            // Model found:
            return l_True;
        }

        // This case may happen only during DTC
        if ( value( next ) != l_Undef )
        {
          assert( config.logic == QF_UFIDL
               || config.logic == QF_UFLRA );
          continue;
        }

        // Increase decision level and enqueue 'next'
        assert(value(next) == l_Undef);
        newDecisionLevel();
        uncheckedEnqueue(next);
    }
  }
}


double CoreSMTSolver::progressEstimate() const
{
  double  progress = 0;
  double  F = 1.0 / nVars();

  for (int i = 0; i <= decisionLevel(); i++){
    int beg = i == 0 ? 0 : trail_lim[i - 1];
    int end = i == decisionLevel() ? trail.size() : trail_lim[i];
    progress += pow(F, i) * (end - beg);
  }

  return progress / nVars();
}

lbool CoreSMTSolver::solve( const vec<Lit> & assumps
                          , const unsigned max_conflicts )
{
  random_seed = config.getRandomSeed();
//  assert( init );
  // Check some invariants before we start ...
  assert( config.logic != UNDEF );
  // Incrementality should be enabled for arrays
  // assert( config.logic != QF_AX || config.incremental );
  // Incrementality should be enabled for lazy dtc
  assert( config.logic != QF_UFRDL || config.sat_lazy_dtc == 0 || config.isIncremental() );
  assert( config.logic != QF_UFIDL || config.sat_lazy_dtc == 0 || config.isIncremental() );
  assert( config.logic != QF_UFLRA || config.sat_lazy_dtc == 0 || config.isIncremental() );
  assert( config.logic != QF_UFLIA || config.sat_lazy_dtc == 0 || config.isIncremental() );
  assert( config.logic != QF_UFLRA || config.sat_lazy_dtc == 0 || config.isIncremental() );
  // UF solver should be enabled for lazy dtc
  assert( config.sat_lazy_dtc == 0 || config.uf_disable == 0 );
#ifdef PRODUCE_PROOF
  // Checks that every variable is associated to a non-zero partition
  if( config.produce_inter > 0 )
  {
    checkPartitions( );
    mixedVarDecActivity( );
  }
#endif

  // Statically inform nodes created so far
//  theory_handler->inform( );

#ifndef SMTCOMP
  if ( config.sat_dump_cnf != 0 )
    dumpCNF( );

//  if ( config.sat_dump_rnd_inter != 0 )
//    dumpRndInter( );
#endif

  model.clear();
  conflict.clear();

  if (!ok) return l_False;

  assumps.copyTo(assumptions);

  double  nof_conflicts = restart_first;
  double  nof_learnts   = nClauses() * learntsize_factor;
  lbool   status        = l_Undef;

  unsigned last_luby_k = luby_k;
#ifndef SMTCOMP
  double next_printout = restart_first;
#endif

  // Search:
  const size_t old_conflicts = nLearnts( );
  // Stop flag for cost theory solving
  bool cstop = false;
  while (status == l_Undef && !opensmt::stop && !cstop)
  {
#ifndef SMTCOMP
    // Print some information. At every restart for
    // standard mode or any 2^n intervarls for luby
    // restarts
    if ( conflicts == 0
	|| conflicts >= next_printout )
    {
//      if ( config.verbosity() > 10 )
      {
	reportf( "; %9d | %8d %8d | %8.3f s | %6.3f MB\n"
	    , (int)conflicts
	    , (int)nof_learnts
	    , nLearnts()
	    , cpuTime( )
	    , memUsed( ) / 1048576.0 );
	fflush( stderr );
      }

      if ( config.sat_use_luby_restart )
	next_printout *= 2;
      else
	next_printout *= restart_inc;
    }
#endif

    status = search((int)nof_conflicts, (int)nof_learnts);
    nof_conflicts = restartNextLimit( nof_conflicts );
    cstop = cstop || ( max_conflicts != 0 
	&& nLearnts() > (int)max_conflicts + (int)old_conflicts );

    if ( config.sat_use_luby_restart )
    {
      if ( last_luby_k != luby_k )
	nof_learnts *= 1.215;
      last_luby_k = luby_k;
    }
    else
      nof_learnts *= learntsize_inc;
  }

  // Added line
  if ( !cstop )
  {
    if (status == l_True){
#ifndef SMTCOMP
      // Extend & copy model:
      model.growTo(nVars());
      for (int i = 0; i < nVars(); i++) model[i] = value(i);
      verifyModel( );
      // Compute models in tsolvers
      if ( config.produce_models
	  && !config.isIncremental() )
      {
//	egraph.computeModel( );
	printModel( );
      }
#endif
    }else{
      assert( opensmt::stop || status == l_False);
      if (conflict.size() == 0)
	ok = false;
    }
  }

  if ( !config.isIncremental() )
  {
    // We terminate
    cancelUntil(-1);
    if ( first_model_found )
      theory_handler.backtrack(-1);
  }
  else
  {
    // We return to level 0,
    // ready to accept new clauses
    cancelUntil(0);
  }

  return status;
}

#ifndef SMTCOMP
/*
lbool CoreSMTSolver::getModel( Enode * atom )
{
  assert( atom->isAtom() );
  Var v = theory_handler->enodeToVar( atom );
  //assert( model[ v ] != l_Undef );
  return model[ v ];
}
*/
#endif

lbool CoreSMTSolver::smtSolve( ) { return solve(); }

int CoreSMTSolver::restartNextLimit ( int nof_conflicts )
{
  // Luby's restart
  if ( config.sat_use_luby_restart )
  {
    if ( ++luby_i == (unsigned) ((1 << luby_k) - 1))
      luby_previous.push_back( 1 << ( luby_k ++ - 1) );
    else
      luby_previous.push_back( luby_previous[luby_i - (1 << (luby_k - 1))]);

    return luby_previous.back() * restart_first;
  }
  // Standard restart
  return nof_conflicts * restart_inc;
}

void CoreSMTSolver::printStatistics( ostream & os )
{
  os << "; -------------------------" << endl;
  os << "; STATISTICS FOR SAT SOLVER" << endl;
  os << "; -------------------------" << endl;
  os << "; Restarts.................: " << starts << endl;
  os << "; Conflicts................: " << conflicts << endl;
  os << "; Decisions................: " << (float)decisions << endl;
  os << "; Propagations.............: " << propagations << endl;
  os << "; Conflict literals........: " << tot_literals << endl;
  os << "; T-Lemmata learnt.........: " << learnt_t_lemmata << endl;
  os << "; T-Lemmata perm learnt....: " << perm_learnt_t_lemmata << endl;
  os << "; Conflicts learnt.........: " << all_learnts << endl;
  os << "; Average learnts size.....: " << learnts_size/all_learnts << endl;
  if ( config.sat_preprocess_booleans != 0
      || config.sat_preprocess_theory != 0 )
    os << "; Preprocessing time.......: " << preproc_time << " s" << endl;
  if ( config.sat_preprocess_theory != 0 )
    os << "; T-Vars eliminated........: " << elim_tvars << " out of " << total_tvars << endl;
  os << "; TSolvers time............: " << tsolvers_time << " s" << endl;
//  if ( config.sat_lazy_dtc != 0 )
//    os << "# Interf. equalities.......: " << ie_generated << " out of " << egraph.getInterfaceTermsNumber( ) * (egraph.getInterfaceTermsNumber( )-1) / 2 << endl;
  os << "; Init clauses.............: " << clauses.size() << endl;
  os << "; Variables................: " << nVars() << endl;
}
