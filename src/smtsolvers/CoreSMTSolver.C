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

#include "time.h"

namespace opensmt
{
  extern bool stop;
}

//=================================================================================================
// Constructor/Destructor:

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
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), conflicts_last_update(0)
  , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  // ADDED FOR MINIMIZATION
  , learnts_size(0) , all_learnts(0), n_clauses(0)
  , learnt_theory_conflicts(0)
  , top_level_lits        (0)
  , ok                    (true)
  , cla_inc               (1)
  , var_inc               (1)
  , latest_round          (0)
  , qhead                 (0)
  , simpDB_assigns        (-1)
  , simpDB_props          (0)
  , order_heap            (VarOrderLt(activity))
  , random_seed           (c.getRandomSeed())
  , progress_estimate     (0)
  , remove_satisfied      (true)
  , LABestLit             (lit_Undef)
  , resource_units        (config.sat_resource_units())
  , resource_limit        (config.sat_resource_limit())
  , next_resource_limit   (-1)
  , split_type            (config.sat_split_type())
  , split_on              (false)
  , split_start           (config.sat_split_asap())
  , split_num             (config.sat_split_num())
  , split_units           (config.sat_split_units())
  , split_inittune        (config.sat_split_inittune())
  , split_midtune         (config.sat_split_midtune())
  , split_next            (split_units == spm_time ? cpuTime() + split_inittune : decisions + split_inittune)
  , split_preference      (sppref_undef)
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
  , preproc_time          (0)
  , elim_tvars            (0)
#endif
  , init                  (false)
#ifdef PEDANTIC_DEBUG
  , max_dl_debug          (0)
  , analyze_cnt           (0)
#endif
{
  vec< Lit > fc;
  fc.push( lit_Undef );
  fake_clause = Clause_new( fc );
}

void
CoreSMTSolver::initialize( )
{
  assert( config.isInit( ) );
//  assert( !init );
  random_seed = config.getRandomSeed();
  restart_first = config.sat_restart_first();
  restart_inc = config.sat_restart_inc();
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

    /*if(SMTConfig::database_host!=NULL){
        struct timeval timeout = {1, 500000}; // 1.5 seconds
        this->clauses_sharing.c_cls_pub = redisConnectWithTimeout(SMTConfig::database_host, SMTConfig::database_port, timeout);
        this->clauses_sharing.c_cls_sub = redisConnectWithTimeout(SMTConfig::database_host, SMTConfig::database_port, timeout);
        if (this->clauses_sharing.c_cls_pub == NULL || this->clauses_sharing.c_cls_sub == NULL) {
            std::cerr << "Connection error: can't use clause sharing!\n";
            redisFree(this->clauses_sharing.c_cls_pub);
            redisFree(this->clauses_sharing.c_cls_sub);
        }
    }*/

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

  LAupperbounds.push(); // leave space for the var
  LAexacts.push();      // leave space for the var
    this->var_seen.push(false);

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

  // Add the deduction entry for this variable
  theory_handler.deductions.push({SolverId_Undef, l_Undef});

  return v;
}

bool CoreSMTSolver::addClause( vec<Lit>& ps
#ifdef PRODUCE_PROOF
                             , ipartitions_t in
#endif
    , bool shared)
{
#ifdef REPORT_DL1_THLITS
  int init_cl_len = ps.size();
#endif
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
#ifdef VERBOSE_SAT
    cerr << toInt(ps[0]) << endl;
#endif
#ifdef REPORT_DL1_THLITS
    if (init_cl_len != 1) {
        // propagation
        char* ulit = theory_handler.getLogic().printTerm(theory_handler.varToTerm(var(ps[0])));
        cerr << "; Made a unit in addClause " << (sign(ps[0]) ? "not " : "") << ulit << endl;
        free(ulit);
    }
#endif
    uncheckedEnqueue(ps[0]);
#ifdef PRODUCE_PROOF
    Clause * confl = propagate();
    if ( confl == NULL ) return ok = true;
    return ok = false;
#else
#ifdef REPORT_DL1_THLITS
    int prev_trail_sz = trail.size();
#endif
    ok = (propagate() == NULL);
#ifdef REPORT_DL1_THLITS
    if (trail.size() > prev_trail_sz+1) {
        cerr << "; Found propagations in addClause:\n";
        for (int i = prev_trail_sz+1; i < trail.size(); i++) {
            char* ulit = theory_handler.getLogic().printTerm(theory_handler.varToTerm(var(trail[i])));
            cerr << ";   " << (sign(trail[i]) ? "not " : "") << ulit << endl;
            free(ulit);
        }
    }
#endif
    return ok;
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
    if(!shared) {
        this->n_clauses += 1;
    }
    attachClause(*c);

#ifdef VERBOSE_SAT
    for (int i = 0; i < c->size(); i++)
      cerr << toInt((*c)[i]) << " ";
    cerr << endl;
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
#ifdef DEBUG_REASONS
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
#ifdef VERBOSE_SAT
  cerr << "restoring " << val_to_restore.size() << " lits to trail" << endl;
#endif
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
    theory_handler.getConflict( conflicting, level, max_decision_level, trail );
#else
    theory_handler.getConflict(conflicting, level, max_decision_level);
#endif
  }
}

//=================================================================================================
// Major methods:

Lit CoreSMTSolver::pickBranchLit(int polarity_mode, double random_var_freq)
{
  Var next = var_Undef;

  // Random decision:
  if (((!split_on && drand(random_seed) < random_var_freq) || (split_on && split_preference == sppref_rand)) && !order_heap.empty()){
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

    vec<int> discarded;

    // Activity based decision:
    while (next == var_Undef || toLbool(assigns[next]) != l_Undef || !decision_var[next]) {
        if (order_heap.empty()){
            if (split_preference == sppref_tterm || split_preference == sppref_bterm) {
                if (discarded.size() > 0)
                    next = discarded[0];
                else next = var_Undef;
            } else
                next = var_Undef;
            break;

        }else {
            next = order_heap.removeMin();
            if (split_on && next != var_Undef) {
                if (split_preference == sppref_tterm && !theory_handler.isTheoryTerm(next)) {
                    discarded.push(next);
                    next = var_Undef;
                } else if (split_preference == sppref_bterm && theory_handler.isTheoryTerm(next)) {
                    discarded.push(next);
                    next = var_Undef;
                }
            }
        }
    }
    if (split_preference == sppref_tterm || split_preference == sppref_bterm)
        for (int i = 0; i < discarded.size(); i++)
            order_heap.insert(discarded[i]);

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
      cancelUntilVar( v );

      vec< Lit > r;
      // Retrieving the reason
#ifdef STATISTICS
      const double start = cpuTime( );
#endif
#ifdef DEBUG_REASONS
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

#ifdef REPORT_DL1_THLITS
  if (out_learnt.size() == 1) {
    char* ulit = theory_handler.getLogic().printTerm(theory_handler.varToTerm(var(out_learnt[0])));
    cerr << "; Found a unit literal " << (sign(out_learnt[0]) ? "not " : "") << ulit << endl;
    free(ulit);
  }
#endif

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
#ifdef DEBUG_REASONS
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
#ifdef DEBUG_REASONS
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
    if (satisfied(*cs[i])) {
        // check if removing from the problem clauses vector: if so then update the index
        if(&cs == &this->clauses && j<this->n_clauses)
            this->n_clauses--;
        removeClause(*cs[i]);
    }
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
#ifdef VERBOSE_SAT
  cerr << "Units when starting search:" << endl;
  for (int i = 2; i < trail.size(); i++) {
    char* name;
    theory_handler.getVarName(var(trail[i]), &name);
    cerr << (sign(trail[i]) ? "not " : "");
    cerr << name << endl;
    ::free(name);
  }
#endif
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

#ifdef STATISTICS
  const double start = cpuTime( );
#endif
  // (Incomplete) Check of Level-0 atoms

  int res = checkTheory( false );
  if ( res == -1 ) return l_False;
  while ( res == 2 ) {
#ifdef REPORT_DL1_THLITS
    
#endif
    res = checkTheory( false );
  }
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
#ifdef PRINT_CLAUSAL_SIZE
  int prev_conflicts = conflicts;
#endif
  while (split_type == spt_none || splits.size() < split_num - 1)
  {
#ifdef PRINT_CLAUSAL_SIZE
    if (conflicts % 1000 == 0 && conflicts != prev_conflicts) {
        prev_conflicts = conflicts;
        printf("; %d total learnt theory conflicts %d\n", conflicts, learnt_theory_conflicts);
    }
#endif
    // Added line
    if ( opensmt::stop ) return l_Undef;

      if (conflicts % 1000 == 0){
          if ( this->stop )
              return l_Undef;
      }
      if (conflicts % 1000 == 0){
          this->clausesPublish();
      }

    if (resource_limit >= 0 && conflicts % 1000 == 0) {
        if ((resource_units == spm_time && time(NULL) >= next_resource_limit) ||
            (resource_units == spm_decisions && decisions >= next_resource_limit)){
            opensmt::stop = true; return l_Undef;
        }
    }

      if(decisionLevel()==0){
          if(conflicts>conflicts_last_update+1000) {
              this->clausesUpdate();
              conflicts_last_update = conflicts;
          }
      }

    Clause* confl = propagate();
    if (confl != NULL){
      // CONFLICT
      conflicts++; conflictC++;
      if (decisionLevel() == 0) {
          if (splits.size() > 0) {
              opensmt::stop = true;
              return l_Undef;
          }
          else return l_False;
      }
      learnt_clause.clear();
      analyze(confl, learnt_clause, backtrack_level);

#ifdef VERBOSE_SAT
      cerr << "Backtracking due to SAT conflict "
           << decisionLevel() - backtrack_level << endl;
      int init_trail_sz = trail.size();
#endif

      cancelUntil(backtrack_level);
#ifdef VERBOSE_SAT
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
      if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
        // Reached bound on number of conflicts:
        progress_estimate = progressEstimate();
        cancelUntil(0);
        return l_Undef; }

        // Simplify the set of problem clauses:
        if (decisionLevel() == 0 && !simplify()) {
            if (splits.size() > 0) {
                opensmt::stop = true;
                return l_Undef;
            } else return l_False;
        }
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
            case -1:
                {
                    if (splits.size() > 0) {
                        opensmt::stop = true;
                        return l_Undef;
                    } else return l_False;  // Top-Level conflict: unsat
                }
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
            if (splits.size() > 0) {
                opensmt::stop = true;
                return l_Undef;
            } else return l_False;
          }else{
            next = p;
            break;
          }
        }

        if (next == lit_Undef)
        {
          // Assumptions done and the solver is in consistent state
          updateSplitState();
          if (!split_start && split_on && scatterLevel()) {
                if (!createSplit_scatter(false)) { // Rest is unsat
                    opensmt::stop = true; return l_Undef; }
                else continue;
          }
          // Otherwise continue to variable decision.


          // New variable decision:
          decisions++;
          next = pickBranchLit(polarity_mode, random_var_freq);
#ifdef VERBOSE_SAT
          char* name;
          if (next != lit_Undef) {
              theory_handler.getVarName(var(next), &name);
              cerr << "branch: " << toInt(next) << (sign(next) ? " not " : " ") << name << endl;
              ::free(name);
          }
          else cerr << "branch: " << toInt(next) << (sign(next) ? " not " : " ") << "undef" << endl;

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
            if ( res == -1 ) {
                if (splits.size() > 0) {
                    opensmt::stop = true;
                    return l_Undef;
                } else return l_False;
            }
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
  cancelUntil(0);
  createSplit_scatter(true);
  opensmt::stop = true; return l_Undef;
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
    // Inform theories of the variables that are actually seen by the
    // SAT solver.
    //bool* var_seen = (bool*)calloc(nVars(), sizeof(bool));
    for (int i = 0; i < trail.size(); i++) {
        Var v = var(trail[i]);
        if (!var_seen[v]) {
            var_seen[v] = true;
            theory_handler.declareTermTree(theory_handler.varToTerm(v));
//            printf("Declaring trail var %s\n", theory_handler.getLogic().printTerm(theory_handler.varToTerm(v)));
        }
    }
    top_level_lits = trail.size();
    for (int i = 0; i < clauses.size(); i++) {
        Clause& c = *clauses[i];
        for (int j = 0; j < c.size(); j++) {
            Var v = var(c[j]);
            if (!var_seen[v]) {
                var_seen[v] = true;
                theory_handler.declareTermTree(theory_handler.varToTerm(v));
//                printf("Declaring clause %d var %s\n", i, theory_handler.getLogic().printTerm(theory_handler.varToTerm(v)));
            }
        }
    }
//    for (int i = 0; i < theory_handler.tsolvers.size(); i++)
//        if (theory_handler.tsolvers[i] != NULL)
//            theory_handler.tsolvers[i]->print(std::cerr);
//    return l_Undef;
    // Forbid branching on the vars that do not appear in the formula.
    // I'm curious as to whether this is sound!
    for (int i = 0; i < nVars(); i++) {
        if (!var_seen[i])
            decision_var[i] = false;
    }
    //free(var_seen);
    // If splitting is enabled refresh the options
    split_type     = config.sat_split_type();
    if (split_type != spt_none) {
        split_start    = config.sat_split_asap();
        split_on       = false;
        split_num      = config.sat_split_num();
        split_inittune = config.sat_split_inittune();
        split_midtune  = config.sat_split_midtune();
        split_units    = config.sat_split_units();
        if (split_units == spm_time)
            split_next = config.sat_split_inittune() + cpuTime();
        else if (split_units == spm_decisions)
            split_next = config.sat_split_inittune() + decisions;
        else split_next = -1;

        split_preference = config.sat_split_preference();

    }
    resource_units = config.sat_resource_units();
    resource_limit = config.sat_resource_limit();
    if (resource_limit >= 0) {
        if (resource_units == spm_time)
            next_resource_limit = cpuTime() + resource_limit;
        else if (resource_units == spm_decisions)
            next_resource_limit = decisions + resource_limit;
    } else next_resource_limit = -1;

    if (config.dump_only()) return l_Undef;

    random_seed = config.getRandomSeed();
//    assert( init );
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
    if (config.produce_inter > 0) {
        checkPartitions( );
        mixedVarDecActivity( );
    }
#endif

#ifndef SMTCOMP
    if ( config.sat_dump_cnf != 0 )
        dumpCNF( );

//    if ( config.sat_dump_rnd_inter != 0 )
//        dumpRndInter( );
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
    // AEJ
//    stop = true;
    while (status == l_Undef && !opensmt::stop && !cstop && !this->stop) {
#ifndef SMTCOMP
        // Print some information. At every restart for
        // standard mode or any 2^n intervarls for luby
        // restarts
        if (conflicts == 0 || conflicts >= next_printout) {
//          if ( config.verbosity() > 10 )
            reportf( "; %9d | %8d %8d | %8.3f s | %6.3f MB\n"
                    , (int)conflicts
                    , (int)nof_learnts
                    , nLearnts()
                    , cpuTime()
                    , memUsed( ) / 1048576.0 );
            fflush( stderr );
        }

        if (config.sat_use_luby_restart)
            next_printout *= 2;
        else
            next_printout *= restart_inc;
#endif
        // XXX
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts = restartNextLimit( nof_conflicts );
        cstop = cstop || ( max_conflicts != 0
            && nLearnts() > (int)max_conflicts + (int)old_conflicts );
        if (config.sat_use_luby_restart) {
            if (last_luby_k != luby_k) {
                nof_learnts *= 1.215;
            }
            last_luby_k = luby_k;
        } else {
            nof_learnts *= learntsize_inc;
        }
    }

    // Added line
    if (!cstop) {
        if (status == l_True) {
#ifndef SMTCOMP
            // Extend & copy model:
            model.growTo(nVars());
            for (int i = 0; i < nVars(); i++) model[i] = value(i);
//            verifyModel();
            // Compute models in tsolvers
            if (config.produce_models() && !config.isIncremental()) {
                printModel();
            }
#endif
        } else {
            assert( opensmt::stop || status == l_False || this->stop);
//      if (conflict.size() == 0)
//          ok = false;
        }
    }

//#ifdef BACKTRACK_AFTER_FINISHING
    if (!config.isIncremental()) {
        // We terminate
        cancelUntil(-1);
        if (first_model_found || splits.size() > 1)
            theory_handler.backtrack(-1);
    } else {
        // We return to level 0,
        // ready to accept new clauses
        cancelUntil(0);
    }

    return status;
}

const CoreSMTSolver::UBel CoreSMTSolver::UBel_Undef(-1, -1);

// safeToSkip: given an exact value e for a variable b, is it safe to
// skip checking my literal's extra value in the lookahead heuristic?
//
bool CoreSMTSolver::UBVal::safeToSkip(const ExVal& e) const
{
    // My value needs to be current with respect to both polarities and
    // the timestamp of e
    if (!current(e)) return false;

    const UBel& ub_l = getLow();
    const UBel& ub_h = getHigh();

    assert(ub_l != UBel_Undef);

    // If my low-polarity upper bound is less than the low exact of b there is
    // no reason to check me
    if (ub_l.ub < e.getEx_l()) {
        return true; }

    // If my low-polarity upper bound is equal to the low exact of b and
    // my high-polarity upper bound is less than or equal to the high
    // exact of b there is no reason to check me
    if (ub_l.ub ==  e.getEx_l() && ub_h.ub <= e.getEx_h()) {
        return true; }

    // In all other cases the value needs to be checked.
    return false;
}

// Entry point for lookaheadSplit
//

lbool CoreSMTSolver::lookaheadSplit(int d)
{
    bool first_model_found_prev = first_model_found;
    first_model_found = true;
    int dl = lookaheadSplit(d, 0, 0);
    lbool res = l_Undef;
    if (dl == -2) {
        res = l_True;
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++)
            model[i] = value(trail[i]);
    }
    else if (splits.size() == 0) {
        res = l_False;
    }
    first_model_found = first_model_found_prev;

    // Without these I get a segfault from theory solver's destructor...
    cancelUntil(-1);
    theory_handler.backtrack(-1);
    return res;
}

lbool CoreSMTSolver::lookaheadSplit2(int d) {
    int idx = 0;
    bool first_model_found_prev = first_model_found;
    first_model_found = true;
    lbool res = lookaheadSplit2(d, idx);
    first_model_found = first_model_found_prev;
    if (res == l_True) {
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++)
            model[i] = value(trail[i]);
    }
    if (res == l_False)
        splits.clear();
    // Without these I get a segfault from theory solver's destructor...
    cancelUntil(-1);
    theory_handler.backtrack(-1);
    return res;
}

// Function for making a propagation.  Returns false if the there was a conflict.
// Backtracks the solver to the correct decision level and continues until no
// new conflicts or propagations are available in theory or in unit propagation
bool CoreSMTSolver::LApropagate_wrapper()
{
    Clause *c;
    bool diff;
    do {
        diff = false;
        while ((c = propagate()) != NULL) {
            vec<Lit> out_learnt;
            int out_btlevel;
            analyze(c, out_learnt, out_btlevel);
#ifdef LADEBUG
            printf("Conflict: I would need to backtrack from %d to %d\n", decisionLevel(), out_btlevel);
#endif
            cancelUntil(out_btlevel);
            Clause* d = NULL;
            if (out_learnt.size() > 1) {
                d = Clause_new(out_learnt, true);
                learnts.push(d);
                attachClause(*d);
            }
            uncheckedEnqueue(out_learnt[0], d);
            diff = true;
        }
        if (!diff) {
            int res = checkTheory(true);
            if (res == -1) {
#ifdef LADEBUG
                printf("Theory unsatisfiability\n");
#endif
                return -1; // Unsat
            } else if (res == 2) {
#ifdef LADEBUG
                printf("Theory propagation\n");
#endif
                diff = true;
                continue;
            } else if (res == 0) {
#ifdef LADEBUG
                printf("Theory conflict\n");
#endif
                diff = true;
            }
        }
    } while (diff);

    return true;
}

// The new try for the lookahead with backjumping:
// Do not write this as a recursive function but instead maintain the
// tree explicitly.  Each internal node should have the info whether its
// both children have been constructed and whether any of its two
// children has been shown unsatisfiable either directly or with a
// backjump.
lbool CoreSMTSolver::lookaheadSplit2(int d, int &idx)
{

    updateRound();
    vec<LANode*> queue;
    LANode* root = new LANode();
    root->p  = root;
    queue.push(root);

    while (queue.size() != 0) {
        LANode& n = *queue.last();
        queue.pop();
#ifdef LADEBUG
        printf("main loop: dl %d -> %d\n", decisionLevel(), 0);
#endif
        cancelUntil(0);

        if (n.v == l_False)
            continue;

        vec<Lit> path;
        LANode *curr = &n;
        LANode* parent = n.p;
        // Collect the truth assignment.
        while (parent != curr) {
            path.push(curr->l);
            curr = parent;
            parent = curr->p;
        }

        int i;
#ifdef LADEBUG
        printf("Setting solver to the right dl %d\n", path.size());
#endif
        for (i = path.size() - 1; i >= 0; i--) {
            newDecisionLevel();
            if (value(path[i]) == l_Undef) {
#ifdef LADEBUG
                printf("I will propagate %s%d\n", sign(path[i]) ? "-" : "", var(path[i]));
#endif
                uncheckedEnqueue(path[i]);
                bool res = LApropagate_wrapper();
                if (res == false) {
#ifdef LADEBUG
                    printf(" -> Path this far is unsatisfiable already\n");
                    printf("Marking the subtree false:\n");
                    n.print();
#endif
                    n.v = l_False;
                    break;
                }
            } else {
#ifdef LADEBUG
                printf("Would propagate %s%d but the literal is already assigned\n", sign(path[i]) ? "-" : "", var(path[i]));
#endif
                if (value(path[i]) == l_False) {
                    n.v = l_False;
#ifdef LADEBUG
                    printf("Unsatisfiable branch since I'd like to propagate %s%d but %s%d is assigned already\n", sign(path[i]) ? "-" : "", var(path[i]), sign(~path[i]) ? "-" : "", var(path[i]));
                    printf("Marking the subtree false:\n");
                    n.print();
#endif
                    break;
                } else {
                    assert(value(path[i]) == l_True);
                }
            }
        }

        // Decision level -1 at this point means we proved unsatisfiability
        if (decisionLevel() == -1)
            return l_False;

        if (i != -1) {
#ifdef LADEBUG
            printf("Unsatisfiability detected on branch\n");
#endif
            continue;
        }
        if (n.d == d) {
#ifdef LADEBUG
            printf("Producing a split:\n");;
            printTrace();
#endif
            createSplit_lookahead();
            continue;
        }

        // Otherwise we will continue here by attempting to create two children for this node

        // Do the lookahead
        assert(decisionLevel() == n.d);
        Lit best;
        lbool res = lookahead_loop(best, idx);
        assert(decisionLevel() <= n.d);

        if (decisionLevel() < n.d) {
#ifdef LADEBUG
            printf("Unsatisfiability detected after lookahead\n");
#endif
            // level and force a backjump.  It means that the node from
            // which backjump happens is unsatisfiable.  It does not
            // mean that the path leading to the lookahead node would be
            // unsatisfiable.  Hence we need to put this node back to
            // the search queue.
            queue.push(&n);
            continue;
        } else if (res == l_True) {
#ifdef LADEBUG
            printf("Lookahead claims to have found a satisfying truth assignment:\n");
            printTrail();
#endif
            return l_True;
        }
        else if (res == l_False)
            return l_False;

        assert(best != lit_Undef);

        LANode* c1 = new LANode(&n, best, l_Undef, n.d+1);
        LANode* c2 = new LANode(&n, ~best, l_Undef, n.d+1);

        queue.push(c1);
        queue.push(c2);

        // These are for debugging
        n.c1 = c1;
        n.c2 = c2;
    }
#ifdef LADEBUG
    root->print();
#endif
    return l_Undef;
}

lbool CoreSMTSolver::lookahead_loop(Lit& best, int &idx) {
    updateRound();
    int i = 0;
    int d = decisionLevel();

    int count = 0;
#ifdef LADEBUG
    printf("Starting lookahead loop with %d vars\n", nVars());
#endif
    for (Var v(idx % nVars()); (LAexacts[v].getRound() != latest_round); v = Var((idx + (++i)) % nVars())) {
#ifdef LADEBUG
        printf("Checking var %d\n", v);
#endif
        if (value(v) != l_Undef || LAupperbounds[v].safeToSkip(LAexacts[var(getLABest())])) {
#ifdef LADEBUG
            printf("  Var is safe to skip due to %s\n",
                value(v) != l_Undef ? "being assigned" : "having low upper bound");
#endif
            LAexacts[v].setRound(latest_round);
            // It is possible that all variables are assigned here.
            // In this case it seems that we have a satisfying assignment.
            // This is in fact a debug check
            if (trail.size() == nVars()) {
                printf("All vars set?\n");
                assert(checkTheory(true) == 1);
                for (int j = 0; j < clauses.size(); j++) {
                    Clause& c = *clauses[j];
                    int k;
                    for (k = 0; k < c.size(); k++) {
                        if (value(c[k]) == l_True) {
                            break;
                        }
                    }
                    assert(k < c.size());
                }
                best = lit_Undef;
                return l_True; // Stands for SAT
            }
            continue;
        }
        count++;
        int p0 = 0, p1 = 0;
        for (int p = 0; p < 2; p++) { // do for both polarities
            assert(decisionLevel() == d);
            newDecisionLevel();
            Lit l(v, p);
            int tmp_trail_sz = trail.size();
#ifdef LADEBUG
            printf("Checking lit %s%d\n", p == 0 ? "" : "-", v);
#endif
            uncheckedEnqueue(l);
            bool res = LApropagate_wrapper();
            if (res == false) { best = lit_Undef; return l_False; }
            if (decisionLevel() == d+1) {
#ifdef LADEBUG
                printf(" -> Successfully propagated %d lits\n", trail.size() - tmp_trail_sz);
#endif
                for (int j = 0; j < trail.size(); j++)
                    updateLAUB(trail[j], trail.size());
            }
            else if (decisionLevel() == d) {
#ifdef LADEBUG
                printf(" -> Propagation resulted in backtrack\n");
#endif
                updateRound();
                break;
            } else {
#ifdef LADEBUG
                printf(" -> Propagation resulted in backtrack: %d -> %d\n", d, decisionLevel());
#endif
                // Backtracking should happen.
                best = lit_Undef;
                return l_Undef;
            }
            p == 0 ? p0 = trail.size() : p1 = trail.size();
            cancelUntil(decisionLevel() - 1);
        }
        if (value(v) == l_Undef) {
#ifdef LADEBUG
            printf("Updating var %d to (%d, %d)\n", v, p0, p1);
#endif
            setLAExact(v, p0, p1);
            updateLABest(v);
            assert(value(getLABest()) == l_Undef);
        }
    }
#ifdef LADEBUG
    printf("Lookahead phase over successfully\n");
    printf("Best I found propagates high %d and low %d\n",
            LAexacts[var(getLABest())].getEx_h(),
            LAexacts[var(getLABest())].getEx_l());
#endif
    idx = (idx + i) % nVars();
    best = getLABest();
    return l_Undef;
}

//
// Do the splits based on the lookahead heuristics.  The function is
// recursive
//  - d is the depth until which the lookahead should be done, and
//    results in 2^d splits
//  - dl is the decision level where the function is called
//  - idx is the index to the variable where the lookahead should start
//    (to avoid the quadratic behavior)
//
int CoreSMTSolver::lookaheadSplit(int d, const int dl, int idx)
{
    assert(decisionLevel() == dl);
    updateRound();
    if (d == 0) { createSplit_lookahead(); return dl; }
    int i = 0;
    bool conflict_found = false;
    printf("Starting lookahead phase at level %d\n", decisionLevel());
    for (Var v(idx % nVars()); (LAexacts[v].getRound() != latest_round) || conflict_found; v = Var((idx + (++i)) % nVars())) {
        if (value(v) != l_Undef || LAupperbounds[v].safeToSkip(LAexacts[var(getLABest())])) {
            LAexacts[v].setRound(latest_round);
            // It is possible that all variables are assigned here.
            // In this case it seems that we have a satisfying assignment.
            if (trail.size() == nVars()) {
                assert(checkTheory(true) == 1);
                for (int j = 0; j < clauses.size(); j++) {
                    Clause& c = *clauses[j];
                    int k;
                    for (k = 0; k < c.size(); k++)
                        if (value(c[k]) == l_True) break;
                    assert(k < c.size());
                }
                return -2; // Stands for SAT
            }
            continue;
        }
        int p0 = 0, p1 = 0;
        for (int p = 0; p < 2; p++) { // do for both polarities

            conflict_found = false;

            if (decisionLevel() == dl)
                newDecisionLevel();
            assert(decisionLevel() == dl+1);
            Lit l(v, p);
            uncheckedEnqueue(l);

            bool diff;
            do {
                assert(decisionLevel() == dl+1 || decisionLevel() == dl);
                diff = false;
                int curr_asgns = trail.size();
                Clause *c;
                while ((c = propagate()) != NULL) {
                    vec<Lit> out_learnt;
                    int out_btlevel;
                    analyze(c, out_learnt, out_btlevel);
                    // Think this better.  If we find a conflict, it
                    // means that the problems at the leaves of the
                    // subtree starting from out_btlevel + 1 are
                    // in fact unsatisfiable.  The exception is the unit
                    // clauses.  
                    printf("Conflict: I need to backtrack from %d to %d\n", decisionLevel(), out_btlevel);
                    printf("The implied literal is %s%d\n", sign(out_learnt[0]) ? "-" : "", var(out_learnt[0]));
                    cancelUntil(out_btlevel);
                    printTrace();
                    Clause* d = NULL;
                    if (out_learnt.size() > 1) {
                        d = Clause_new(out_learnt, true);
                        learnts.push(d);
                        attachClause(*d);
                    }
                    uncheckedEnqueue(out_learnt[0], d);
                    if (out_btlevel < dl) { // Backjump
                        if (out_btlevel == -1)
                            return out_btlevel;
                        else return out_btlevel+1; // To be consistent with the recursive call in normal case
                    }
                    conflict_found = true;
                    diff = true;
                    assert(decisionLevel() == dl);
                }
                if (!diff) {
                    int res = checkTheory(true);
                    if (res == -1) return -1;
                    if (res == 2) {
                        printf("Theory propagations\n");
                        propagations = true;
                        continue; // BCP
                    }
                    if (res == 0) { // l results in a conflict.
                        printf("Theory conflict\n");
                        printTrace();
                        if (decisionLevel() < dl) // Backjump
                            return decisionLevel();
                        // The propagation can be continued until fix point
                        // We can still continue the lookahead, but we are
                        // no longer interested in the upper bounds
                        conflict_found = true;
                        diff = true;
                    }
                }
                diff |= (trail.size() - curr_asgns > 0);
            } while (diff);

            if (!conflict_found)
                for (int j = 0; j < trail.size(); j++)
                    updateLAUB(trail[j], trail.size());
            else {
                // Which also means that there is new information
                // available on the solver in the form of literals
                // asserted on the previous decision level and we need
                // to recompute the lookahead values.
                updateRound();
                assert(decisionLevel() == dl);
                break;
            }

            p == 0 ? p0 = trail.size() : p1 = trail.size();

            // Backtrack the decision
            cancelUntil(decisionLevel()-1);
        }

        if (!conflict_found && value(v) == l_Undef) {
            setLAExact(v, p0, p1);
            updateLABest(v);
            assert(value(getLABest()) == l_Undef);
        }
    }
    printf("Lookahead phase over successfully\n");
    assert(decisionLevel() == dl);
    Lit best = getLABest();  // Save the best lit for this round
    // FIXME here it is possible not to have a best literal, for
    // instance if everything is already assigned.
    assert(best != lit_Undef);
    assert(value(best) == l_Undef);
    printf("The best I found propagates high %d and low %d\n", LAexacts[var(getLABest())].getEx_h(), LAexacts[var(getLABest())].getEx_l());
    for (int p = 0; p < 2; p++) { // repeat for both polarities
        // Make the branch
        newDecisionLevel();
        Lit choice = p == 0 ? best : ~best;
        printTrace();
        printf("I'm making decision %s%d at dl %d\n", sign(choice) ? "-" : "", var(choice), decisionLevel());
        uncheckedEnqueue(choice);
        assert(decisionLevel() == dl+1);
        int new_dl = lookaheadSplit(d-1, decisionLevel(), idx);
        if (new_dl <= dl)
            return new_dl;
//        assert(decisionLevel() == dl+1); // This is not true
        cancelUntil(dl);
    }
    assert(decisionLevel() == dl);
    return dl;
}

void CoreSMTSolver::updateLABest(Var v)
{
    assert(value(v) == l_Undef);
    ExVal& e = LAexacts[v];
    Lit l_v = Lit(v, e.betterPolarity());
    if (value(LABestLit) != l_Undef)
        LABestLit = l_v;
    else {
        Lit prev_best = getLABest();
        LABestLit = LAexacts[v] < LAexacts[var(prev_best)] ? prev_best : l_v;
    }
}

void CoreSMTSolver::updateLAUB(Lit l, int props)
{
    UBVal& val = LAupperbounds[var(l)];
    if (sign(l))
        val.updateUB_n(UBel(props, latest_round));
    else
        val.updateUB_p(UBel(props, latest_round));
}

void CoreSMTSolver::setLAExact(Var v, int pprops, int nprops)
{
    LAexacts[v] = ExVal(pprops, nprops, latest_round);
    if (LABestLit != lit_Undef)
        LABestLit = LAexacts[var(LABestLit)] < LAexacts[v] ? Lit(v, nprops > pprops) : LABestLit;
    else LABestLit = Lit(v, nprops > pprops);
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

bool CoreSMTSolver::scatterLevel()
{
    int d;
    if (!split_on) return false;
    // Current scattered instance number i = splits.size() + 1
    float r = 1/(float)(split_num-splits.size());
    for (int i = 0; ; i++) {
        // 2 << i == 2^(i+1)
        if ((2 << (i-1) <= split_num - splits.size()) &&
                (2 << i >= split_num - splits.size())) {
            // r-1(2^i) < 0 and we want absolute
            d = -(r-1/(float)(2<<(i-1))) > r-1/(float)(2<<i) ? i+1 : i;
            break;
        }
    }
    return d == decisionLevel();
}

bool CoreSMTSolver::createSplit_lookahead()
{
    // Due to the stupidness of the minisat version this gets
    // complicated
    int curr_dl0_idx = trail_lim.size() > 0 ? trail_lim[0] : trail.size();
    splits.push_c(SplitData(clauses, trail, curr_dl0_idx));
    SplitData& sp = splits.last();

    printf("; Outputing an instance:\n; ");
    for (int i = 0; i < decisionLevel(); i++) {
        vec<Lit> tmp;
        Lit l = trail[trail_lim[i]];
        tmp.push(l);
        printf("%s%d ", sign(l) ? "-" : "", var(l));
        sp.addConstraint(tmp);
    }
    printf("\n");
    sp.updateInstance();
    assert(ok);
    return true;
}

bool CoreSMTSolver::createSplit_scatter(bool last)
{
    // Due to the stupidness of the minisat version this gets
    // complicated
    int curr_dl0_idx = trail_lim.size() > 0 ? trail_lim[0] : trail.size();
    splits.push_c(SplitData(clauses, trail, curr_dl0_idx));
    SplitData& sp = splits.last();
    vec<Lit> constraints_negated;
    for (int i = 0; i < decisionLevel(); i++) {
        vec<Lit> tmp;
        Lit l = trail[trail_lim[i]];
        tmp.push(l);
        sp.addConstraint(tmp);
        constraints_negated.push(~l);
    }
    sp.updateInstance();
    // XXX Skipped learned clauses
    cancelUntil(0);
    if (!excludeAssumptions(constraints_negated))
        return false;
    simplify();
    assert(ok);
    split_start = true;
    split_on    = true;
    split_next = (split_units == spm_time ? cpuTime() + split_midtune : decisions + split_midtune);
    return true;
}

bool CoreSMTSolver::excludeAssumptions(vec<Lit>& neg_constrs)
{
    addClause(neg_constrs);
    simplify();
    return ok;
}

void CoreSMTSolver::updateSplitState()
{
    if (split_start && !split_on) {
        if ((split_units == spm_time && cpuTime() >= split_next) ||
                (split_units == spm_decisions && decisions >= split_next)) {
            cancelUntil(0);
            split_start = false;
            split_on = true;
            if (split_units == spm_time) split_next = cpuTime() + split_midtune;
            if (split_units == spm_decisions) split_next = decisions + split_midtune;
        }
    }
    if (split_start && split_on) {
        if ((split_units == spm_time && cpuTime() >= split_next) ||
                (split_units == spm_decisions && decisions >= split_next)) {
            cancelUntil(0);
            split_start = false;
            split_on = true;
            if (split_units == spm_time) split_next = cpuTime() + split_midtune;
            if (split_units == spm_decisions) split_next = decisions + split_midtune;
        }
    }
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
  os << "; T-conflicts learnt.......: " << learnt_theory_conflicts << endl;
  os << "; Average learnts size.....: " << learnts_size/all_learnts << endl;
  os << "; Top level literals.......: " << top_level_lits << endl;
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

//void CoreSMTSolver::clausesPublish() {
//    if (this->clauses_sharing.channel.empty() || this->clauses_sharing.c_cls_pub == NULL || this->clauses_sharing.c_cls_pub->err != 0)
//        return;
//    std::string s;
//    for (int i = 0; i < this->learnts.size(); i++) {
//        Clause &c = *this->learnts[i];
//        if (c.mark() != 3) {
//            clauseSerialize(c, s);
//            c.mark(3);
//        }
//    }
//    if (s.length() == 0)
//        return;
//    Message m;
//
//    struct sockaddr_in sin;
//    int addrlen = sizeof(sin);
//    getsockname(this->clauses_sharing.c_cls_pub->fd, (struct sockaddr *) &sin, (socklen_t *) &addrlen);
//    m.header["from"].append(inet_ntoa(sin.sin_addr));
//    m.header["from"].append(":");
//    m.header["from"].append(std::to_string(sin.sin_port));
//
//    m.payload = s;
//    std::string d;
//    m.dump(d);
//
//    redisReply *reply = (redisReply *) redisCommand(this->clauses_sharing.c_cls_pub, "PUBLISH %s.out %b", this->clauses_sharing.channel.c_str(), d.c_str(),
//                                                    d.length());
//    if (reply == NULL)
//        std::cerr << "Connection error during clause publishing\n";
//    freeReplyObject(reply);
//    /* non block
//    redisCommand(this->c_cls_pub, "PUBLISH %s.out %b", this->channel, d.c_str(), d.length());
//    this->flush(this->c_cls_pub);
//    if (this->c_cls_pub->err != 0)
//        cerr << "Redis publish connection lost\n"; */
//}


//void CoreSMTSolver::clausesUpdate() {
//    if (this->clauses_sharing.channel.empty() || this->clauses_sharing.c_cls_sub == NULL || this->clauses_sharing.c_cls_sub->err != 0)
//        return;
//    /* non block
//    redisReply *reply;
//    redisBufferRead(this->c_cls_sub);
//    if (redisGetReplyFromReader(this->c_cls_sub, (void **) &reply) != REDIS_OK)
//        cerr << "Redis subscribe connection lost\n";
//    if (reply == NULL)
//        return;
//    assert (reply->type == REDIS_REPLY_ARRAY && reply->elements == 3);
//    assert (std::string(reply->element[0]->str).compare("message") == 0);
//    std::string s = std::string(reply->element[2]->str, reply->element[2]->len); */
////ZREVRANGEBYSCORE %s +inf 0 LIMIT 0 10000
//    redisReply *reply = (redisReply *) redisCommand(this->clauses_sharing.c_cls_sub, "SRANDMEMBER %s 10000",
//                                                    this->clauses_sharing.channel.c_str());
//    if (reply == NULL) {
//        std::cerr << "Connection error during clause updating\n";
//        return;
//    }
//    if (reply->type != REDIS_REPLY_ARRAY)
//        return;
//
//    for (int i = this->n_clauses; i < this->clauses.size(); i++) {
//        if (i < this->n_clauses + reply->elements)
//            this->removeClause(*this->clauses[i]);
//        if (i + reply->elements < this->clauses.size())
//            this->clauses[i] = this->clauses[i + reply->elements];
//    }
//    this->clauses.shrink(std::min(this->clauses.size() - this->n_clauses, (uint32_t) reply->elements));
//
//
//    for (int i = 0; i < reply->elements; i++) {
//        std::string str = std::string(reply->element[i]->str, reply->element[i]->len);
//        vec<Lit> lits;
//        uint32_t o = 0;
//        clauseDeserialize(str, &o, lits);
//        bool f=false;
//        for(int j=0; j<lits.size(); j++){
//            if(!this->var_seen[var(lits[j])]) {
//                f=true;
//                break;
//            }
//        }
//        if(!f)
//            this->addClause(lits, true);
//    }
///*
//    if (reply->type != REDIS_REPLY_STRING)
//        return;
//    std::string s = std::string(reply->str, reply->len);
//    Message m;
//    m.load(s);
//    //if (m.header.find("from") != m.header.end()) if (m.header["from"].compare(...) == 0)
//    //  return;
//    uint32_t o = 0;
//    while (o < m.payload.length()) {
//        vec<Lit> lits;
//        clauseDeserialize(m.payload, &o, lits);
//        solver.addClause(lits, true);
//    }
//*/
//    freeReplyObject(reply);
//}
