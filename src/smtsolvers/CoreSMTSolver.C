/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2016 Antti Hyvarinen
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
#include "Sort.h"
#include <cmath>

#ifdef PRODUCE_PROOF
#include "Proof.h"
#endif

namespace opensmt
{
    extern bool stop;
}

//=================================================================================================
// Constructor/Destructor:

CoreSMTSolver::CoreSMTSolver(SMTConfig & c, THandler& t )
    : SMTSolver        (c, t)
    , axioms_checked   ( 0 )
    , verbosity        (c.verbosity())
    // Parameters: (formerly in 'SearchParams')
    , var_decay        (c.sat_var_decay())
    , clause_decay     (c.sat_clause_decay())
    , random_var_freq  (c.sat_random_var_freq())
    , luby_restart     (c.sat_luby_restart())
    , ccmin_mode       (c.sat_ccmin_mode())
    , phase_saving     (c.sat_pcontains())
    , rnd_pol          (c.sat_rnd_pol())
    , rnd_init_act     (c.sat_rnd_init_act())
    , garbage_frac     (c.sat_garbage_frac())
    , restart_first    (c.sat_restart_first())
    , restart_inc      (c.sat_restart_inc())
    , learntsize_factor((double)1/(double)3)
    , learntsize_inc   ( 1.1 )
      // More parameters:
      //
    , expensive_ccmin  ( true )
    , learntsize_adjust_start_confl (0)
      // Statistics: (formerly in 'SolverStats')
      //
    , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), conflicts_last_update(0)
    , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
      // ADDED FOR MINIMIZATION
    , learnts_size(0) , all_learnts(0), n_clauses(0)
    , learnt_theory_conflicts(0)
    , top_level_lits        (0)
    , la_tl_unsat           (laresult::tl_unsat)
    , la_sat                (laresult::sat)
    , la_restart            (laresult::restart)
    , la_unsat              (laresult::unsat)
    , la_ok                 (laresult::ok)
    , ok                    (true)
    , cla_inc               (1)
    , var_inc               (1)
    , watches               (WatcherDeleted(ca))
    , latest_round          (0)
    , qhead                 (0)
    , simpDB_assigns        (-1)
    , simpDB_props          (0)
    , order_heap            (VarOrderLt(activity))
    , random_seed           (c.getRandomSeed())
    , progress_estimate     (0)
    , remove_satisfied      (true)
    , buf_LABests           (c.randomize_lookahead_bufsz(), assigns, c.randomize_lookahead(), c.getRandomSeed())
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
    , unadvised_splits      (0)
    , forced_split          (lit_Undef)
    , learnt_t_lemmata      (0)
    , perm_learnt_t_lemmata (0)
    , luby_i                (0)
    , luby_k                (1)
    , cuvti                 (false)
#ifdef PRODUCE_PROOF
    , proof_                ( new Proof( ca ) )
    , proof                 ( * proof_ )
    , proof_graph           ( NULL )
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
    , conflict_budget       (-1)
    , propagation_budget    (-1)
    , asynch_interrupt      (false)
{ }

void
CoreSMTSolver::initialize( )
{
    assert( config.isInit( ) );
//  assert( !init );
    random_seed = config.getRandomSeed();
    restart_first = config.sat_restart_first();
    restart_inc = config.sat_restart_inc();
    // FIXME: check why this ?
//    first_model_found = config.logic == QF_UFLRA
//                        || config.logic == QF_UFIDL;
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
    case 0:
        polarity_mode = polarity_true;
        break;
    case 1:
        polarity_mode = polarity_false;
        break;
    case 2:
        polarity_mode = polarity_rnd;
        break;
    case 3:
        polarity_mode = polarity_user;
        break; // Polarity is set in
    case 4:
        polarity_mode = polarity_user;
        break; // THandler.C for
    case 5:
        polarity_mode = polarity_user;
        break; // Boolean atoms
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

    for (int i = 0; i < units.size(); i++)   if(units[i] != CRef_Undef)   ca.free(units[i]);
    for (int i = 0; i < clauses.size(); i++) if(clauses[i] != CRef_Undef) ca.free(clauses[i]);
    for (int i = 0; i < pleaves.size(); i++) if(pleaves[i] != CRef_Undef) ca.free(pleaves[i]);
    for (int i = 0; i < learnts.size(); i++) if(learnts[i] != CRef_Undef) ca.free(learnts[i]);
    for (int i = 0; i < axioms.size(); i++) if(axioms[i] != CRef_Undef) ca.free(axioms[i]);
    for (int i = 0; i < tleaves.size(); i++) if(tleaves[i] != CRef_Undef) ca.free(tleaves[i]);

#else
    for (int i = 0; i < learnts.size(); i++) ca.free(learnts[i]);
    for (int i = 0; i < clauses.size(); i++) ca.free(clauses[i]);
    for (int i = 0; i < axioms .size(); i++) ca.free(axioms [i]);
#endif

    for (int i = 0; i < tmp_reas.size(); i++) ca.free(tmp_reas[i]);

#ifdef STATISTICS
    if ( config.produceStats() != 0 ) printStatistics ( config.getStatsOut( ) );
    // TODO added for convenience
    if ( config.print_stats != 0 ) printStatistics ( cerr );

#endif

#ifdef PRODUCE_PROOF
    delete proof_;
#endif
}

//=================================================================================================
// Minor methods:
//
// Add a new var v to the solver if it does not yet exist
//
void CoreSMTSolver::addVar(Var v)
{
    if (v < nVars()) {
        // These are Necessary in incremental mode since previously
        // ignored vars can now reappear
        insertVarOrder(v);
        decision[v] = true;
        return;
    }
    while (v >= nVars())
        newVar();
}

// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var CoreSMTSolver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
#ifdef PRODUCE_PROOF
    trail_pos.push(-1);
    units    .push( CRef_Undef );
#endif

    polarity    .push((char)sign);

#if CACHE_POLARITY
    prev_polarity.push(toInt(l_Undef));
#endif

    LAupperbounds.push(); // leave space for the var
    LAexacts.push();      // leave space for the var
    this->var_seen.push(false);

    insertVarOrder(v);

    // Added Lines
    // Skip undo for varTrue and varFalse
    if ( v != 0 && v != 1 )
        undo_stack.push(undo_stack_el(undo_stack_el::NEWVAR, v));

    n_occs.push(0);

    // Add the deduction entry for this variable
    theory_handler.pushDeduction();

    return v;
}

#ifdef PRODUCE_PROOF
bool CoreSMTSolver::addClause_(vec<Lit>& _ps, const ipartitions_t& mask)
{
    CRef cr;
    return addClause_(_ps, cr, mask);
}
#else
bool CoreSMTSolver::addClause_(vec<Lit>& _ps)
{
    CRef cr;
    return addClause_(_ps, cr);
}
#endif

#ifdef PRODUCE_PROOF
bool CoreSMTSolver::addClause_(vec<Lit>& _ps, CRef& cr_o, const ipartitions_t& mask)
#else
bool CoreSMTSolver::addClause_(vec<Lit>& _ps, CRef& cr_o)
#endif
{
    cr_o = CRef_Undef;

#ifdef PRODUCE_PROOF
    Logic& logic = theory_handler.getLogic();
    bool resolved = false;
    CRef root = CRef_Undef;
#endif
    vec<Lit> ps;
    _ps.copyTo(ps);

    if (!ok) return false;
    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p;
    int i, j;
#ifdef PRODUCE_PROOF
    root = ca.alloc( ps, false );
    logic.addClauseClassMask(root, mask);
    for(int lt = 0; lt < ps.size(); ++lt) {
        logic.addVarClassMask(var(ps[lt]), mask);
    }
    proof.addRoot( root, CLA_ORIG );
    assert( config.isInit( ) );
    proof.beginChain( root );
#endif
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
    {
        if ((value(ps[i]) == l_True && vardata[var(ps[i])].level == 0) || ps[i] == ~p)
        {
#ifdef PRODUCE_PROOF
            proof.endChain( );
            proof.forceDelete( root );
#endif
            // decrease the counts of those encountered so far
            for (int k = 0; k < j; k++)
            {
                n_occs[var(ps[k])] -= 1;
                assert(n_occs[var(ps[k])] >= 0);
            }
            return true;
        }
        else if ((value(ps[i]) != l_False || vardata[var(ps[i])].level > 0) && ps[i] != p)
        {
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
    }
    ps.shrink(i - j);

    if (ps.size() == 0)
    {
#ifdef PRODUCE_PROOF
        proof.endChain( CRef_Undef );
        tleaves.push( root );
#endif
        return ok = false;
    }

#ifdef PRODUCE_PROOF
    CRef res = CRef_Undef;
    if ( resolved )
    {
        res = ca.alloc( ps, false );
        logic.addClauseClassMask(res, mask);
        for(int lt = 0; lt < ps.size(); ++lt)
            logic.addVarClassMask(var(ps[lt]), mask);
        assert( ca[res].size( ) < ca[root].size( ) );
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

    if (ps.size() == 1)
    {
        assert(decisionLevel() == 0);
        assert(value(ps[0]) == l_Undef);
#ifdef PRODUCE_PROOF
        assert( res != CRef_Undef );
        assert( units[ var(ps[0]) ] == CRef_Undef );
        units[ var(ps[0]) ] = res;
#endif
#ifdef VERBOSE_SAT
        cerr << toInt(ps[0]) << endl;
#endif
#ifdef REPORT_DL1_THLITS
        if (init_cl_len != 1)
        {
            // propagation
            char* ulit = theory_handler.getLogic().printTerm(theory_handler.varToTerm(var(ps[0])));
            cerr << "; Made a unit in addClause " << (sign(ps[0]) ? "not " : "") << ulit << endl;
            free(ulit);
        }
#endif
        uncheckedEnqueue(ps[0]);
#ifdef PRODUCE_PROOF
        CRef confl = propagate();
        if ( confl == CRef_Undef ) return ok = true;
        return ok = false;
#else
#ifdef REPORT_DL1_THLITS
        int prev_trail_sz = trail.size();
#endif
        ok = (propagate() == CRef_Undef);
#ifdef REPORT_DL1_THLITS
        if (trail.size() > prev_trail_sz+1)
        {
            cerr << "; Found propagations in addClause:\n";
            for (int i = prev_trail_sz+1; i < trail.size(); i++)
            {
                char* ulit = theory_handler.getLogic().printTerm(theory_handler.varToTerm(var(trail[i])));
                cerr << ";   " << (sign(trail[i]) ? "not " : "") << ulit << endl;
                free(ulit);
            }
        }
#endif
        return ok;
#endif
    }
    else
    {

#ifdef PRODUCE_PROOF
        CRef cr = res;
#else
        CRef cr = ca.alloc(ps, false);
#endif
      cr_o = cr;
#ifdef PRODUCE_PROOF
        /*
            if ( config.isIncremental() )
            {
              undo_stack.push_back( NEWPROOF );
              undo_stack_el.push_back( (void *)cr );
            }
        */
#endif
        if (ca[cr].size() != 1) {
            clauses.push(cr);
            attachClause(cr);
        }

        undo_stack.push(undo_stack_el(undo_stack_el::NEWCLAUSE, cr));
    }

    return true;
}


void CoreSMTSolver::attachClause(CRef cr)
{
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size();
}

void CoreSMTSolver::detachClause(CRef cr, bool strict)
{
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    if (strict)
    {
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }
    else
    {
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size();
}

void CoreSMTSolver::removeClause(CRef cr)
{
    Clause& c = ca[cr];
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
#ifdef PRODUCE_PROOF
    // Remove clause and derivations if ref becomes 0
    // If ref is not 0, we keep it and remove later
    if ( !proof.deleted( cr ) ) pleaves.push( cr );
#else
    ca.free(cr);
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
        for (int c = trail.size()-1; c >= trail_lim[level]; c--)
        {
            Var      x  = var(trail[c]);
#ifdef PEDANTIC_DEBUG
            assert(assigns[x] != l_Undef);
#endif
            assigns [x] = l_Undef;
            if (phase_saving > 1 || ((phase_saving == 1) && c > trail_lim.last()))
                polarity[x] = sign(trail[c]);
            insertVarOrder(x);
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);

        //if ( first_model_found )
        theory_handler.backtrack(trail.size());
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
        assigns[ x ] = l_Undef;
        insertVarOrder( x );
    }

    // Reset v itself
    assigns[ v ] = l_Undef;
    insertVarOrder( v );

    trail.shrink(trail.size( ) - c );
    qhead = trail.size( );

    if ( decisionLevel( ) > level(v) )
    {
        assert( c > 0 );
        assert( c - 1 < trail.size( ) );
        assert( var(trail[ c ]) == v );

        int lev = level(var(trail[ c-1 ]));
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
        assigns[x] = l_Undef;
    }
    // Stores v as well
    Lit p = trail[ c ];
    Var x = var( p );
    assert( v == x );
    lit_to_restore.push( p );
    val_to_restore.push(assigns[x]);
    assigns[x] = l_Undef;

    // Reset v itself
    assigns[v] = l_Undef;

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
        Lit p = lit_to_restore.last();
        Var x = var(p);
        lit_to_restore.pop();
        lbool v = val_to_restore.last();
        val_to_restore.pop();
        assigns[x] = v;
        trail.push(p);
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
        theory_handler.getConflict( conflicting, vardata, max_decision_level, trail );
#else
        theory_handler.getConflict(conflicting, vardata, max_decision_level);
#endif
    }
}

//=================================================================================================
// Major methods:

Lit CoreSMTSolver::pickBranchLit()
{
    if (forced_split != lit_Undef) {
        Lit fs = forced_split;
        forced_split = lit_Undef;
        return fs;
    }

    Var next = var_Undef;

    // Random decision:
    if (((!split_on && drand(random_seed) < random_var_freq) || (split_on && split_preference == sppref_rand)) && !order_heap.empty())
    {
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++;
    }

    // Theory suggestion-based decision
    for( ;; )
    {
        Lit sugg = lit_Undef; //= theory_handler->getSuggestion( );
        // No suggestions
        if ( sugg == lit_Undef )
            break;
        // Atom already assigned or not to be used as decision
        if ( value(sugg) != l_Undef || !decision[var(sugg)] )
            continue;
        // If here, good decision has been found
        return sugg;
    }

    vec<int> discarded;

//    printf("Activity (%d)\n", activity.size());
//    for (int i = 0; i < activity.size(); i++)
//        printf("%f ", activity[i]);
//    printf("\n");
    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
    {
        if (order_heap.empty())
        {
            if (split_preference == sppref_tterm || split_preference == sppref_bterm)
            {
                if (discarded.size() > 0)
                    next = discarded[0];
                else next = var_Undef;
            }
            else
                next = var_Undef;
            break;

        }
        else
        {
            next = order_heap.removeMin();
            if (split_on && next != var_Undef)
            {
                if (split_preference == sppref_tterm && !theory_handler.isTheoryTerm(next))
                {
                    discarded.push(next);
                    next = var_Undef;
                }
                else if (split_preference == sppref_bterm && theory_handler.isTheoryTerm(next))
                {
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

    return next == var_Undef ? lit_Undef : mkLit(next, sign);
}

#ifdef PRODUCE_PROOF
class lastToFirst_lt    // Helper class to 'analyze' -- order literals from last to first occurance in 'trail[]'.
{
    const vec<int>& trail_pos;
public:
    lastToFirst_lt(const vec<int>& t) : trail_pos(t) {}
    bool operator () (Lit p, Lit q)
    {
        return trail_pos[var(p)] > trail_pos[var(q)];
    }
};
#endif

/*_________________________________________________________________________________________________
  |
  |  analyze : (confl : CRef) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
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

void CoreSMTSolver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    CRef confl_orig = confl;
#ifdef PRODUCE_PROOF
    assert( proof.checkState( ) );
#endif
    assert(confl != CRef_Undef);
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

    do
    {
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++)
        {
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0)
            {
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                // Variable propagated at current level
                if (level(var(q)) >= decisionLevel())
                    // Increment counter for number of pivot variables left on which to resolve
                    pathC++;
                else
                {
                    // Variable propagated at previous level
                    out_learnt.push(q);
                }
            }
#ifdef PRODUCE_PROOF
            else if (!seen[var(q)])
            {
                if ( level( var(q) ) == 0 )
                {
                    proof.resolve( units[ var( q ) ], var( q ) );
                }
            }
#endif
        }
        // Select next clause to look at:
        while (!seen[var(trail[index--])])
            ; // Do nothing
        assert(index >= 0);
        p     = trail[index+1];

        if ( reason(var(p)) == CRef_Fake )
        {
            // Before retrieving the reason it is necessary to backtrack
            // a little bit in order to remove every atom pushed after
            // p has been deduced
            Var v = var(p);
            assert(value(p) == l_True);
            // Backtracking the trail until v is the variable on the top
            cancelUntilVar( v );

            vec<Lit> r;
            // Retrieving the reason
#ifdef STATISTICS
            const double start = cpuTime( );
#endif
#ifdef DEBUG_REASONS
            if (theory_handler.getReason( p, r, assigns ) == false)
            {
                assert(debug_reason_map.has(var(p)));
                int idx = debug_reason_map[var(p)];
                CRef cr = debug_reasons[idx];
                cerr << "Could not find reason " << theory_handler.printAsrtClause(c) << endl;
                assert(false);
            }
#else
            theory_handler.getReason(p, r);
#endif
            assert(r.size() > 0);
#ifdef STATISTICS
            tsolvers_time += cpuTime( ) - start;
#endif

            CRef ctr = CRef_Undef;
            if ( r.size() > config.sat_learn_up_to_size )
            {
                ctr = ca.alloc(r);
                cleanup.push(ctr);
            }
            else
            {
                bool learnt_ = config.sat_temporary_learn;
                ctr = ca.alloc(r, learnt_);
                learnts.push(ctr);
                attachClause(ctr);
                undo_stack.push(undo_stack_el(undo_stack_el::NEWLEARNT, ctr));
                claBumpActivity(ca[ctr]);
                learnt_t_lemmata ++;
                if ( !config.sat_temporary_learn )
                    perm_learnt_t_lemmata ++;
            }
            assert( ctr != CRef_Undef );
            vardata[var(p)].reason = ctr;
#ifdef PRODUCE_PROOF
            proof.addRoot(ctr, CLA_THEORY);
            /*if ( config.isIncremental() )
            {
                undo_stack_oper.push_back( NEWPROOF );
                undo_stack_elem.push_back( (void *)ct );
            }*/

            if ( config.produce_inter() > 0 )
            {
                // Enode * interpolants = theory_handler->getInterpolants( );
                // assert( interpolants );
                // clause_to_in[ ct ] = interpolants;
                /*if ( config.isIncremental() )
                {
                    undo_stack_oper.push_back( NEWINTER );
                    undo_stack_elem.push_back( NULL );
                }*/
            }
#endif
        }

        confl = reason(var(p));

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
        //  AH: Do also remember that the first literal of the clause needs to be the implying literal.
        assert( pathC == 1 || confl != CRef_Undef );
        seen[var(p)] = 0;
        pathC--;
#ifdef PRODUCE_PROOF
        if ( pathC > 0 )
        {
            proof.resolve(confl, var(p));
        }
#endif
    }
    while (pathC > 0);

    assert(p != lit_Undef);
    assert((~p) != lit_Undef);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2)
    {
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)
#ifdef PRODUCE_PROOF
        analyze_proof.clear( );
#endif

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];

    }
    else if (ccmin_mode == 1)
    {
        // Added line
        assert( false );
        for (i = j = 1; i < out_learnt.size(); i++)
        {
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else
            {
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0)
                    {
                        out_learnt[j++] = out_learnt[i];
                        break;
                    }
            }
        }
    }
    else
        i = j = out_learnt.size();
    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else
    {
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

#ifdef REPORT_DL1_THLITS
    if (out_learnt.size() == 1)
    {
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
        Var v = var( analyze_proof[ k ] );
        assert( level(v) > 0 );
        // Skip decision variables
        assert(reason(v) != CRef_Undef);
        CRef c = reason( v );
        proof.resolve(c, v);
        // Look for level 0 unit clauses
        Clause& cla = ca[ c ];
        for (int k = 1; k < cla.size(); k++)
        {
            Var vv = var(cla[k]);
            if (level( vv ) == 0) proof.resolve( units[ vv ], vv );
        }
    }
    // Chain will be ended outside analyze
#endif

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

    // Cleanup generated lemmata
    for ( int i = 0 ; i < cleanup.size() ; i ++ )
    {
#ifdef PRODUCE_PROOF
        // Theory lemma automatically cleaned
        tleaves.push( cleanup[ i ] );
#else
        ca.free(cleanup[i]);
#endif
    }

//    for (int i = 0; i < out_learnt.size(); i++)
//        printf("%d ", out_learnt[i]);
//    printf("\n");
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

    analyze_stack.clear();
    analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0)
    {
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        CRef cr = reason(var(analyze_stack.last()));
        if ((config.sat_minimize_conflicts >= 2) && (cr == CRef_Fake))
        {
            // Before retrieving the reason it is necessary to backtrack
            // a little bit in order to remove every atom pushed after
            // p has been deduced
            Lit p = analyze_stack.last();
            Var v = var(p);
            vec< Lit > r;
            // Temporairly backtracking
            cancelUntilVarTempInit( v );
            // Retrieving the reason
#ifdef DEBUG_REASONS
            if (theory_handler.getReason( p, r, assigns ) == false)
            {
                assert(debug_reason_map.has(var(p)));
                int idx = debug_reason_map[var(p)];
                Clause* c = debug_reasons[idx];
                cerr << theory_handler.printAsrtClause(c) << endl;
                assert(false);
            }
#else
            theory_handler.getReason(p, r);
#endif
            // Restoring trail
            cancelUntilVarTempDone( );
            CRef ct = CRef_Undef;
            if ( r.size( ) > config.sat_learn_up_to_size )
            {
                ct = ca.alloc(r);
                tmp_reas.push(ct);
            }
            else
            {
                ct = ca.alloc(r, config.sat_temporary_learn);
                learnts.push(ct);
                if (config.isIncremental() != 0)
                    undo_stack.push(undo_stack_el(undo_stack_el::NEWLEARNT, ct));
                attachClause(ct);
                claBumpActivity(ca[ct]);
                learnt_t_lemmata ++;
                if ( !config.sat_temporary_learn )
                    perm_learnt_t_lemmata ++;
            }
            vardata[v].reason = ct;
#ifdef PRODUCE_PROOF
            /* NOTE : THEORY INTERPOLATION NOT YET SUPPORTED
            proof.addRoot( ct, CLA_THEORY );
            if ( config.isIncremental() )
            {
                undo_stack_oper.push_back( NEWPROOF );
                undo_stack_elem.push_back( (void *)ct );
            }
            if ( config.produce_inter() > 0 )
            {
                Enode * interpolants = theory_handler->getInterpolants( );
                assert( interpolants );
                clause_to_in[ ct ] = interpolants;
                if ( config.isIncremental() )
                {
                    undo_stack_oper.push_back( NEWINTER );
                    undo_stack_elem.push_back( NULL );
                }
            }
            */
#endif
        }
        else
        {
            assert(config.sat_minimize_conflicts == 1);
            // Just give up when fake reason is found -- but clean analyze_toclear
            if (cr == CRef_Fake)
            {
                for (int j = top; j < analyze_toclear.size(); j++)
                seen[var(analyze_toclear[j])] = 0;
                analyze_toclear.shrink(analyze_toclear.size() - top);

                return false;
            }
        }

        Clause& c = ca[cr];

        analyze_stack.pop();

        for (int i = 1; i < c.size(); i++)
        {
            Lit p  = c[i];

            if (!seen[var(p)] && level(var(p)) > 0)
            {
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0)
                {
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }
                else
                {
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
//#ifdef PRODUCE_PROOF
//    opensmt_error( "case not handled (yet)" );
//#endif
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--)
    {
        Var x = var(trail[i]);
        if (seen[x])
        {
            if (reason(x) == CRef_Undef)
            {
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }
            else
            {
                if (reason(x) == CRef_Fake)
                {
                    cancelUntilVarTempInit(x);
                    vec<Lit> r;
                    theory_handler.getReason(trail[i], r);
                    assert(r.size() > 0);
                    for (int j = 1; j < r.size(); j++)
                        if (level(var(r[j])) > 0)
                            seen[var(r[j])] = 1;
                    cancelUntilVarTempDone();
                }
                else
                {
                    Clause& c = ca[reason(x)];
                    for (int j = 1; j < c.size(); j++)
                        if (level(var(c[j])) > 0)
                            seen[var(c[j])] = 1;
                }
                seen[x] = 0;
            }
        }
    }

    seen[var(p)] = 0;
}


void CoreSMTSolver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(from != CRef_Fake || theory_handler.getLogic().isTheoryTerm(theory_handler.varToTerm(var(p))));
#ifdef DEBUG_REASONS
    assert(from == CRef_Fake || !debug_reason_map.has(var(p)));
#endif
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());

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
CRef CoreSMTSolver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size())
    {
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;)
        {
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True)
            {
                *j++ = *i++;
                continue;
            }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;

            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            Watcher w = Watcher(cr, first);
            if (first != blocker && value(first) == l_True)
            {
                *j++ = w;
                continue;
            }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False)
                {
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                }

#ifdef PRODUCE_PROOF
            // Did not find watch -- clause is unit under assignment:
            if (decisionLevel() == 0)
            {
                proof.beginChain( cr );
                for (int k = 1; k < c.size(); k++)
                {
                    assert(level(var(c[k])) == 0);
                    proof.resolve( units[var(c[k])], var(c[k]) );
                }

                assert( units[ var(first) ] == CRef_Undef || value( first ) == l_False );    // (if variable already has 'id', it must be with the other polarity and we should have derived the empty clause here)
                if ( value(first) != l_False )
                {
                    vec<Lit> tmp;
                    tmp.push(first);
                    CRef uc = ca.alloc( tmp );
                    proof.endChain( uc );
                    assert( units[ var(first) ] == CRef_Undef );
                    units[var(first)] = uc;
                }
                else
                {
                    vec<Lit> tmp;
                    tmp.push(first);
                    CRef uc = ca.alloc( tmp );
                    proof.endChain(uc);
                    pleaves.push(uc);
                    // Empty clause derived:
                    proof.beginChain(units[var(first)]);
                    proof.resolve(uc, var(first));
                    proof.endChain( CRef_Undef );
                }
            }
#endif

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False)
            {
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }
            else
                uncheckedEnqueue(first, cr);

NextClause:
            ;
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
struct reduceDB_lt
{
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y)
    {
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity());
    }
};
void CoreSMTSolver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++)
    {
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
#ifdef PRODUCE_PROOF
    /* NOTE old code
    // Remove unused theory lemmata
    for ( i = j = 0 ; i < tleaves.size( ) ; i++ ){
        // RB: Not clear if it is safe, probably not
        // Remove if satisfied at dec level 0
        if (decisionLevel( ) == 0 && satisfied( *tleaves[i] ))
            proof.forceDelete( tleaves[i], true );
        else
	{
            if ( proof.deleted( tleaves[i] ) )
                ; // Do nothing
            else
                tleaves[j++] = tleaves[i];
	}
    }
    tleaves.shrink(i - j);

    // Remove unused leaves
    for ( i = j = 0 ; i < pleaves.size( ) ; i++ )
    {
        // RB: Not clear if it is safe, probably not
        // Remove if satisfied at dec level 0
        if (decisionLevel( ) == 0 && satisfied( *pleaves[i] ))
            proof.forceDelete( pleaves[i], true );
        else
        {
            if ( proof.deleted( pleaves[i] ) )
                ; // Do nothing
            else
                pleaves[j++] = pleaves[i];
        }
    }
    pleaves.shrink(i - j);
    */

    // Remove unused leaves
    // FIXME deal with theory lemmata when proofs will be extended to theories
    for ( i = j = 0 ; i < pleaves.size( ) ; i++ )
    {
        CRef cr = pleaves[i];
        assert(ca[cr].mark() == 1);
        if ( ! proof.deleted( cr ) ) pleaves[j++] = pleaves[i];
    }
    pleaves.shrink(i - j);

#endif
}


void CoreSMTSolver::removeSatisfied(vec<CRef>& cs)
{
    int i,j;
    for (i = j = 0; i < cs.size(); i++)
    {
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}

void CoreSMTSolver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
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

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    // removeSatisfied(axioms);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    // rebuildOrderHeap();
    order_heap.filter(VarFilter(*this));

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

void
CoreSMTSolver::pushBacktrackPoint()
{
    assert( config.isIncremental() );
    //
    // Save undo stack size
    //
    undo_stack_size.push(undo_stack.size( ));
    undo_trail_size.push(trail.size( ));
#ifdef PRODUCE_PROOF
    proof.pushBacktrackPoint( );
#endif
}

void CoreSMTSolver::popBacktrackPoint()
{
    assert( config.isIncremental() );
    //
    // Force restart, but retain assumptions
    //
    cancelUntil(0);
    //
    // Shrink back trail
    //
    int new_trail_size = undo_trail_size.last();
    undo_trail_size.pop();
    for ( int i = trail.size( ) - 1 ; i >= new_trail_size ; i -- )
    {
        Var     x  = var(trail[i]);
        assigns[x] = l_Undef;
        vardata[x].reason = CRef_Undef;
        insertVarOrder(x);
    }
    trail.shrink(trail.size( ) - new_trail_size);
    assert( trail_lim.size( ) == 0 );
    qhead = trail.size( );
    //
    // Undo operations
    //
    size_t new_stack_size = undo_stack_size.last();
    undo_stack_size.pop();
    while ( undo_stack.size( ) > new_stack_size )
    {
        const undo_stack_el op = undo_stack.last();

        if (op.getType() == undo_stack_el::NEWVAR)
        {
            const Var x = op.getVar();

            // Undoes insertVarOrder( )
            assert( order_heap.inHeap(x) );
            order_heap  .remove(x);
            // Undoes decision_var ... watches
            decision    .pop();
            polarity    .pop();
            seen        .pop();
            activity    .pop();
            vardata     .pop();
            assigns     .pop();
            watches.clean(mkLit(x, true));
            watches.clean(mkLit(x, false));
            // Remove variable from translation tables
//      theory_handler->clearVar( x );
        }
        else if (op.getType() == undo_stack_el::NEWUNIT) ; // Do nothing
        else if (op.getType() == undo_stack_el::NEWCLAUSE)
        {
            CRef cr = op.getClause();
            assert( clauses.last() == cr );
            clauses.pop();
            removeClause(cr);
        }
        else if (op.getType() == undo_stack_el::NEWLEARNT)
        {
            CRef cr = op.getClause();
            detachClause(cr);
            detached.push(cr);
        }
        else if (op.getType() == undo_stack_el::NEWAXIOM)
        {
            CRef cr = op.getClause();
            assert(axioms.last() == cr);
            axioms.pop();
            removeClause(cr);
        }
#ifdef PRODUCE_PROOF
        else if (op.getType() == undo_stack_el::NEWPROOF)
        {
            assert( false );
        }
        else if (op.getType() == undo_stack_el::NEWINTER) ; // Do nothing. Ids are never reset ...
#endif
        else
        {
            opensmt_error2( "unknown undo operation in CoreSMTSolver", op.getType() );
        }

        undo_stack.pop();
    }
    //
    // Clear all learnts
    //
    while( learnts.size( ) > 0 )
    {
        CRef cr = learnts.last();
        learnts.pop( );
        removeClause(cr);
    }
#ifdef PRODUCE_PROOF
    proof.popBacktrackPoint( );
#endif
    assert( learnts.size( ) == 0 );
    // Backtrack theory solvers
    theory_handler.backtrack(trail.size());
    // Restore OK
    restoreOK( );
    assert( isOK( ) );
}

bool CoreSMTSolver::okContinue()
{
    // Added line
    if ( opensmt::stop ) return false;

    if (conflicts % 1000 == 0) {
        if ( this->stop )
            return false;
    }
    if (resource_limit >= 0 && conflicts % 1000 == 0) {
        if ((resource_units == spm_time && time(NULL) >= next_resource_limit) ||
            (resource_units == spm_decisions && decisions >= next_resource_limit)) {
            opensmt::stop = true;
            return false;
        }
    }
    return true;
}

void CoreSMTSolver::learntSizeAdjust() {
    if (--learntsize_adjust_cnt == 0) {
        learntsize_adjust_confl *= learntsize_adjust_inc;
        learntsize_adjust_cnt = (int) learntsize_adjust_confl;
        max_learnts *= learntsize_inc;

        if (verbosity >= 1)
            fprintf(stderr, ";| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
                    (int) conflicts,
                    (int) dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(),
                    (int) clauses_literals,
                    (int) max_learnts, nLearnts(), (double) learnts_literals / nLearnts(), progressEstimate() * 100);
    }
}

void CoreSMTSolver::runPeriodics()
{
    if (conflicts % 1000 == 0)
        clausesPublish();

    if (decisionLevel() == 0) {
        if (conflicts > conflicts_last_update + 1000) {
            clausesUpdate();
            conflicts_last_update = conflicts;
        }
    }
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
    // Time my executionto search_timer
//    opensmt::StopWatch stopwatch = opensmt::StopWatch(search_timer);
#ifdef VERBOSE_SAT
    cerr << "Units when starting search:" << endl;
    for (int i = 2; i < trail.size(); i++)
    {
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

    bool first = true;

#ifdef STATISTICS
    const double start = cpuTime( );
#endif
    // (Incomplete) Check of Level-0 atoms

    TPropRes res = checkTheory(false, conflictC);
    if ( res == TPropRes::Unsat) return l_False;

    assert( res == TPropRes::Decide || res == TPropRes::Propagate ); // Either good for decision (from TSolver's perspective) or propagate
#ifdef STATISTICS
    tsolvers_time += cpuTime( ) - start;
#endif

    //
    // Decrease activity for booleans
    //
//    boolVarDecActivity( );

#ifdef PEDANTIC_DEBUG
    bool thr_backtrack = false;
#endif
    while (split_type == spt_none || splits.size() < split_num - 1)
    {
        if (!okContinue())
            return l_Undef;
        runPeriodics();


        CRef confl = propagate();
        if (confl != CRef_Undef)
        {
            // CONFLICT
            conflicts++;
            conflictC++;
            if (decisionLevel() == 0)
            {
                if (splits.size() > 0)
                {
                    opensmt::stop = true;
                    return l_Undef;
                }
                else return l_False;
            }
            first = false;
            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);

            cancelUntil(backtrack_level);

            assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1)
            {
                uncheckedEnqueue(learnt_clause[0]);
#ifdef PRODUCE_PROOF
                CRef cr = ca.alloc( learnt_clause, false );
                proof.endChain( cr );
                assert( units[ var(learnt_clause[0]) ] == CRef_Undef );
                units[ var(learnt_clause[0]) ] = proof.last( );
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
#endif
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            learntSizeAdjust();
        }
        else
        {
            // NO CONFLICT
            if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) || !withinBudget())
            {
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef;
            }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
            {
                if (splits.size() > 0)
                {
                    opensmt::stop = true;
                    return l_Undef;
                }
                else return l_False;
            }
            // Two ways of reducing the clause.  The latter one seems to be working
            // better (not running proper tests since the cluster is down...)
            // if ((learnts.size()-nAssigns()) >= max_learnts)
            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

//            if ( first_model_found )
            {
                // Early Pruning Call
                // Step 1: check if the current assignment is theory-consistent

                TPropRes res = checkTheory(false, conflictC);
                if (res == TPropRes::Unsat) {
                    if (splits.size() > 0) {
                        opensmt::stop = true;
                        return l_Undef;
                    }
                    else return l_False;    // Top-Level conflict: unsat
                }
                else if (res == TPropRes::Propagate) {
                    continue; // Theory conflict: time for bcp
                }
                else if (res == TPropRes::Decide) {
                    ;                 // Sat and no deductions: go ahead
                }
                else {
                    assert( false );
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
            while (decisionLevel() < assumptions.size())
            {
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True)
                {
                    // Dummy decision level:
                    newDecisionLevel();
                }
                else if (value(p) == l_False)
                {
                    analyzeFinal(~p, conflict);
                    if (splits.size() > 0)
                    {
                        opensmt::stop = true;
                        return l_Undef;
                    }
                    else return l_False;
                }
                else
                {
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef)
            {
                // Assumptions done and the solver is in consistent state
                updateSplitState();
                if (!split_start && split_on && scatterLevel())
                {
                    if (!createSplit_scatter(false))   // Rest is unsat
                    {
                        opensmt::stop = true;
                        return l_Undef;
                    }
                    else continue;
                }
                // Otherwise continue to variable decision.


                // New variable decision:
                decisions++;
                next = pickBranchLit();
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
//                    first_model_found = true;
#ifdef STATISTICS
                    const double start = cpuTime( );
#endif
                    TPropRes res = checkTheory(true, conflictC);
#ifdef STATISTICS
                    tsolvers_time += cpuTime( ) - start;
#endif
                    if ( res == TPropRes::Propagate )
                    {
                        continue;
                    }
                    if ( res == TPropRes::Unsat )
                    {
                        if (splits.size() > 0)
                        {
                            opensmt::stop = true;
                            return l_Undef;
                        }
                        else return l_False;
                    }
                    assert( res == TPropRes::Decide );

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
                    next = pickBranchLit();
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
    opensmt::stop = true;
    return l_Undef;
}


double CoreSMTSolver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++)
    {
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}


/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x)
{

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x)
    {
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

void CoreSMTSolver::declareVarsToTheories()
{
    // First empty the solver
    theory_handler.clear();
    for (int i = 0; i < var_seen.size(); i++)
        var_seen[i] = false;

    for (int i = 0; i < trail.size(); i++)
    {
        Var v = var(trail[i]);
        if (!var_seen[v])
        {
            var_seen[v] = true;
            theory_handler.declareTermTree(theory_handler.varToTerm(v));
        }
    }
    top_level_lits = trail.size();
    for (int i = 0; i < clauses.size(); i++)
    {
        Clause& c = ca[clauses[i]];
        for (int j = 0; j < c.size(); j++)
        {
            Var v = var(c[j]);
            if (!var_seen[v])
            {
                var_seen[v] = true;
                assert(theory_handler.getLogic().getPterm(theory_handler.varToTerm(v)).getVar() != -1);
                theory_handler.declareTermTree(theory_handler.varToTerm(v));
//                printf("Declaring clause %d var %s\n", i, theory_handler.getLogic().printTerm(theory_handler.varToTerm(v)));
            }
        }
    }

    // Forbid branching on the vars that do not appear in the formula.
    // I'm curious as to whether this is sound!
    for (int i = 0; i < nVars(); i++)
    {
        if (!var_seen[i])
        {
            setDecisionVar(decision[i], false);
#ifdef PEDANTIC_DEBUG
            cerr << "Disabling var " << theory_handler.getLogic().printTerm(theory_handler.varToTerm(i)) << endl;
#endif
        }
    }
}

lbool CoreSMTSolver::solve_(int max_conflicts)
{
//    opensmt::PrintStopWatch watch("solve time", cerr);

    this->clausesUpdate();

    // Inform theories of the variables that are actually seen by the
    // SAT solver.
    declareVarsToTheories();

    split_type     = config.sat_split_type();
    if (split_type != spt_none)
    {
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
    if (resource_limit >= 0)
    {
        if (resource_units == spm_time)
            next_resource_limit = cpuTime() + resource_limit;
        else if (resource_units == spm_decisions)
            next_resource_limit = decisions + resource_limit;
    }
    else next_resource_limit = -1;

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
    /*
    // Checks that every variable is associated to a non-zero partition
    if (config.produce_inter > 0) {
        checkPartitions( );
        mixedVarDecActivity( );
    }
    */
#endif

    if ( config.sat_dump_cnf != 0 )
        dumpCNF( );

//    if ( config.sat_dump_rnd_inter != 0 )
//        dumpRndInter( );
    model.clear();
    conflict.clear();

    if (!ok) return l_False;

    solves++;

    double  nof_conflicts     = restart_first;
    double  nof_learnts       = nClauses() * learntsize_factor;
    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    unsigned last_luby_k = luby_k;

    if (verbosity >= 1)
    {
        fprintf(stderr, "; ============================[ Search Statistics ]==============================\n");
        fprintf(stderr, "; | Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        fprintf(stderr, "; |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        fprintf(stderr, "; ===============================================================================\n");
    }
    double next_printout = restart_first;

    // Search:
    const size_t old_conflicts = nLearnts( );
    // Stop flag for cost theory solving
    bool cstop = false;
    if (config.dryrun())
        stop = true;
    while (status == l_Undef && !opensmt::stop && !cstop && !this->stop)
    {
        // Print some information. At every restart for
        // standard mode or any 2^n intervarls for luby
        // restarts
        if (conflicts == 0 || conflicts >= next_printout)
        {
          if ( config.verbosity() > 0 ) {
              reportf("; %9d | %8d %8d | %8.3f s | %6.3f MB\n", (int) conflicts, (int) learnts.size(), nLearnts(),
                      cpuTime(), memUsed() / 1048576.0);
              fflush(stderr);
          }
        }

        if (config.sat_use_luby_restart)
            next_printout *= 2;
        else
            next_printout *= restart_inc;
        // XXX
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts = restartNextLimit( nof_conflicts );
        cstop = cstop || ( max_conflicts != 0
                           && nLearnts() > (int)max_conflicts + (int)old_conflicts );
        if (config.sat_use_luby_restart)
        {
            if (last_luby_k != luby_k)
            {
                nof_learnts *= 1.215;
            }
            last_luby_k = luby_k;
        }
        else
        {
            nof_learnts *= learntsize_inc;
        }
    }

    // Added line
    if (!cstop)
    {
        if (status == l_True)
        {
            // Extend & copy model:
            model.growTo(nVars());
            for (int i = 0; i < nVars(); i++) model[i] = value(i);
//            verifyModel();
            // Compute models in tsolvers
            if (config.produce_models() && !config.isIncremental())
            {
                printModel();
            }
        }
        else
        {
            assert( opensmt::stop || status == l_False || this->stop);
//      if (conflict.size() == 0)
//          ok = false;
        }
    }

    // We terminate
//    clearSearch();

    return status;
}

void CoreSMTSolver::clearSearch()
{
    cancelUntil(0);
//    if (first_model_found || splits.size() > 1) {
        theory_handler.backtrack(-1);
//    }
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
    if (ub_l.ub < e.getEx_l())
    {
        return true;
    }

    // If my low-polarity upper bound is equal to the low exact of b and
    // my high-polarity upper bound is less than or equal to the high
    // exact of b there is no reason to check me
    if (ub_l.ub ==  e.getEx_l() && ub_h.ub <= e.getEx_h())
    {
        return true;
    }

    // In all other cases the value needs to be checked.
    return false;
}

lbool CoreSMTSolver::lookaheadSplit(int d)
{
    declareVarsToTheories();

    double nof_conflicts = restart_first;
    const size_t old_conflicts = nLearnts();

    int idx = 0;
//    bool first_model_found_prev = first_model_found;
//    first_model_found = true;
    lbool res = l_Undef;
    while (res == l_Undef) {
        //cerr << "; Doing lookahead for " << nof_conflicts << " conflicts\n";
        ConflQuota conflict_quota;
        if (false) { //if (config.lookahead_restarts()) {
            conflict_quota = ConflQuota((int)nof_conflicts);
        }
        res = lookaheadSplit(d, idx, conflict_quota);

        nof_conflicts = restartNextLimit(nof_conflicts);
    }
//    first_model_found = first_model_found_prev;
    if (res == l_True)
    {
        model.growTo(nVars());
        for (int i = 0; i < dec_vars; i++) // TODO: Fix this at some point
            model[i] = value(trail[i]);
    }
    if (res == l_False)
        splits.clear();
    // Without these I get a segfault from theory solver's destructor...
    cancelUntil(0);
    theory_handler.backtrack(0);
    return res;
}

//
// Function for making a propagation.
// max_confl is a bound on the number of conflicts the wrapper is allowed to do
// Returns l_Undef if the bound on conflicts is reached.
// Returns l_False if the there was a conflict.
// Returns l_True if there was no conflict.
//
// Backtracks the solver to the correct decision level and continues until no
// new conflicts or propagations are available in theory or in unit propagation
//

lbool CoreSMTSolver::LApropagate_wrapper(ConflQuota& confl_quota)
{
    CRef cr;
    bool diff;
    do
    {
        diff = false;
        while ((cr = propagate()) != CRef_Undef)
        {
            if (decisionLevel() == 0)
                return l_False; // Unsat
            -- confl_quota;
#ifdef LADEBUG
            cerr << "; Got a conflict, quota now " << confl_quota << "\n";
#endif
            if (confl_quota <= 0)
                return l_Undef;

            vec<Lit> out_learnt;
            int out_btlevel;
            analyze(cr, out_learnt, out_btlevel);
#ifdef LADEBUG
            printf("Conflict: I would need to backtrack from %d to %d\n", decisionLevel(), out_btlevel);
#endif
            cancelUntil(out_btlevel);
            assert(value(out_learnt[0]) == l_Undef);
            if (out_learnt.size() == 1)
            {
                uncheckedEnqueue(out_learnt[0]);
            }
            else
            {
                CRef crd = ca.alloc(out_learnt, true);
                learnts.push(crd);
                attachClause(crd);
                uncheckedEnqueue(out_learnt[0], crd);

            }
            diff = true;
        }
        if (!diff)
        {
            TPropRes res = checkTheory(true);
            if (res == TPropRes::Unsat)
            {
#ifdef LADEBUG
                printf("Theory unsatisfiability\n");
#endif
                return l_False; // Unsat
            }
            else if (res == TPropRes::Propagate)
            {
#ifdef LADEBUG
                printf("Theory propagation / conflict\n");
#endif
                diff = true;
                -- confl_quota;
#ifdef LADEBUG
                cerr << "; Got a theory conflict, quota now " << confl_quota << "\n";
#endif
                if (confl_quota <= 0)
                    return l_Undef;
            }
        }
    } while (diff);

    return l_True;
}

// The new try for the lookahead with backjumping:
// Do not write this as a recursive function but instead maintain the
// tree explicitly.  Each internal node should have the info whether its
// both children have been constructed and whether any of its two
// children has been shown unsatisfiable either directly or with a
// backjump.
//
// The parameter d is the maximum depth of a path, used for splitting.
// If d < 0, there is no maximum depth and the search continues on a
// branch until it is shown unsatisfiable.
// parameter idx store where we were last time in checking the variables
// confl_quota is the maximum number of conflicts that we're allowed to collect before a restart
//
lbool CoreSMTSolver::lookaheadSplit(int d, int &idx, ConflQuota confl_quota)
{
    int la_split_count = 0;

    updateRound();
    vec<LANode*> queue;
    LANode* root = new LANode();
    root->p  = root;
    queue.push(root);

    while (queue.size() != 0)
    {
//        printf("LA split count %d\n", la_split_count++);
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
        while (parent != curr)
        {
            path.push(curr->l);
            curr = parent;
            parent = curr->p;
        }

        int i;
#ifdef LADEBUG
        printf("Setting solver to the right dl %d\n", path.size());
#endif
        for (i = path.size() - 1; i >= 0; i--)
        {
            newDecisionLevel();
            if (value(path[i]) == l_Undef)
            {
#ifdef LADEBUG
                printf("I will propagate %s%d\n", sign(path[i]) ? "-" : "", var(path[i]));
#endif
                int curr_dl = decisionLevel();
                uncheckedEnqueue(path[i]);
                lbool res = LApropagate_wrapper(confl_quota);
                // Here it is possible that the solver is on level 0 and in an inconsistent state.  How can I check this?
                if (res == l_False) {
                    return l_False; // Indicate unsatisfiability
                }
                else if (res == l_Undef) {
                    cancelUntil(0);
                    return l_Undef; // Do a restart
                }
                if (curr_dl != decisionLevel())
                {

//                    cerr << " -> Path this far is unsatisfiable already\n";
//                    cerr << "Marking the subtree false:\n";
//                    n.print();

                    n.v = l_False;
                    break;
                }
            }
            else
            {
#ifdef LADEBUG
                printf("Would propagate %s%d but the literal is already assigned\n", sign(path[i]) ? "-" : "", var(path[i]));
#endif
                if (value(path[i]) == l_False)
                {
                    n.v = l_False;
#ifdef LADEBUG
                    printf("Unsatisfiable branch since I'd like to propagate %s%d but %s%d is assigned already\n", sign(path[i]) ? "-" : "", var(path[i]), sign(~path[i]) ? "-" : "", var(path[i]));
                    printf("Marking the subtree false:\n");
                    n.print();
#endif
                    break;
                }
                else
                {
                    assert(value(path[i]) == l_True);
                }
            }
        }

        if (i != -1)
        {
#ifdef LADEBUG
            printf("Unsatisfiability detected on branch\n");
#endif
            continue;
        }
        if ((d >= 0) && n.d == d)
        {
#ifdef LADEBUG
            printf("Producing a split:\n");;
            printTrace();
#endif
            createSplit_lookahead();
            if (config.sat_split_test_cube_and_conquer())
                return l_Undef; // The cube-and-conquer experiment
            else
                continue;
        }

        // Otherwise we will continue here by attempting to create two children for this node

        // Do the lookahead
        assert(decisionLevel() == n.d);
        Lit best;
        laresult res = lookahead_loop(best, idx, confl_quota);
        assert(decisionLevel() <= n.d);

        if (res == la_tl_unsat) {
            return l_False;
        }
        else if (res == la_restart) {
            return l_Undef;
        }
        else if (res == la_unsat)
        {
            assert(decisionLevel() < n.d);
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
        }
        else if (res == la_sat)
        {
#ifdef LADEBUG
            printf("Lookahead claims to have found a satisfying truth assignment:\n");
            printTrail();
#endif
            return l_True;
        }
        assert(res == la_ok);
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

CoreSMTSolver::laresult CoreSMTSolver::lookahead_loop(Lit& best, int &idx, ConflQuota &confl_quota)
{
    ConflQuota unlimited;
    if (LApropagate_wrapper(unlimited) == l_False)
    {
#ifdef LADEBUG
        printf("Already unsatisfiable at entering the lookahead loop\n");
#endif
        return la_tl_unsat;
    }

    updateRound();
    int i = 0;
    int d = decisionLevel();

    int count = 0;
    bool respect_logic_partitioning_hints = config.respect_logic_partitioning_hints();
    int skipped_vars_due_to_logic = 0;

#ifdef LADEBUG
    printf("Starting lookahead loop with %d vars\n", nVars());
#endif
    for (Var v(idx % nVars()); (LAexacts[v].getRound() != latest_round); v = Var((idx + (++i)) % nVars()))
    {
        if (!decision[v]) {
            LAexacts[v].setRound(latest_round);
#ifdef LADEBUG
            printf("Not a decision variable: %d (%s)\n", v, theory_handler.getLogic().printTerm(theory_handler.varToTerm(v)));
#endif
            continue; // Skip the non-decision vars
        }
        if (v == (idx * nVars()) && skipped_vars_due_to_logic > 0)
            respect_logic_partitioning_hints = false; // Allow branching on these since we looped back.
        if (respect_logic_partitioning_hints && !(theory_handler.getLogic().okToPartition(theory_handler.varToTerm(v)))) {
            skipped_vars_due_to_logic ++;
            printf("Skipping %d since logic says it's not good\n", v);
            continue; // Skip the vars that the logic considers bad to split on
        }
#ifdef LADEBUG
        printf("Checking var %d\n", v);
#endif
        Lit best = buf_LABests.getLit();
        if (value(v) != l_Undef || (best != lit_Undef && LAupperbounds[v].safeToSkip(LAexacts[var(best)])))
        {
#ifdef LADEBUG
            printf("  Var is safe to skip due to %s\n",
                   value(v) != l_Undef ? "being assigned" : "having low upper bound");
//            if (value(v) == l_Undef)
//                printf("  Var is safe to skip due to having low upper bound\n");
#endif
            LAexacts[v].setRound(latest_round);
            // It is possible that all variables are assigned here.
            // In this case it seems that we have a satisfying assignment.
            // This is in fact a debug check
            if (trail.size() == dec_vars)
            {
#ifdef LADEBUG
                printf("All vars set?\n");
#endif
                if (checkTheory(true) != TPropRes::Decide) // TODO could also be tpr_Propagate
                    return la_tl_unsat; // Problem is trivially unsat
                assert(checkTheory(true) == TPropRes::Decide);
#ifdef LADEBUG
                for (int j = 0; j < clauses.size(); j++)
                {
                    Clause& c = ca[clauses[j]];
                    int k;
                    for (k = 0; k < c.size(); k++)
                    {
                        if (value(c[k]) == l_True)
                        {
                            break;
                        }
                    }
                    assert(k < c.size());
                }
#endif
                best = lit_Undef;
                return la_sat; // Stands for SAT
            }
            continue;
        }
        if (trail.size() == nVars() + skipped_vars_due_to_logic) {
            printf("; %d vars were skipped\n", skipped_vars_due_to_logic);
            respect_logic_partitioning_hints = false;
            continue;
        }
        count++;
        int p0 = 0, p1 = 0;
        for (int p = 0; p < 2; p++)   // do for both polarities
        {
            assert(decisionLevel() == d);
            newDecisionLevel();
            Lit l = mkLit(v, p);
            int tmp_trail_sz = trail.size();
#ifdef LADEBUG
           printf("Checking lit %s%d\n", p == 0 ? "" : "-", v);
#endif
            uncheckedEnqueue(l);
            lbool res = LApropagate_wrapper(confl_quota);
            if (res == l_False)
            {
                best = lit_Undef;
                return la_tl_unsat;
            }
            else if (res == l_Undef)
            {
                cancelUntil(0);
                return la_restart;
            }
            // Else we go on
            if (decisionLevel() == d+1)
            {
#ifdef LADEBUG
                printf(" -> Successfully propagated %d lits\n", trail.size() - tmp_trail_sz);
#endif
                for (int j = 0; j < trail.size(); j++)
                    updateLAUB(trail[j], trail.size());
            }
            else if (decisionLevel() == d)
            {
#ifdef LADEBUG
                printf(" -> Propagation resulted in backtrack\n");
#endif
                updateRound();
                break;
            }
            else
            {
#ifdef LADEBUG
                printf(" -> Propagation resulted in backtrack: %d -> %d\n", d, decisionLevel());
#endif
                // Backtracking should happen.
                best = lit_Undef;
                return la_restart;
            }
            p == 0 ? p0 = trail.size() : p1 = trail.size();
            // Update also the clause deletion heuristic?
            cancelUntil(decisionLevel() - 1);
        }
        if (value(v) == l_Undef)
        {
#ifdef LADEBUG
           printf("Updating var %d to (%d, %d)\n", v, p0, p1);
#endif
            setLAExact(v, p0, p1);
            updateLABest(v);
            assert(value(buf_LABests.getLit()) == l_Undef);
        }
    }
    if (trail.size() == dec_vars && buf_LABests.getLit() == lit_Undef)
    {
#ifdef LADEBUG
        printf("All variables are already set, so we have nothing to branch on and this is a SAT answer\n");
#endif
        return la_sat;
    }
    best = buf_LABests.getLit();
    assert(best != lit_Undef);
#ifdef LADEBUG
    printf("Lookahead phase over successfully\n");
    printf("Best I found propagates high %d and low %d\n",
           LAexacts[var(best)].getEx_h(),
           LAexacts[var(best)].getEx_l());
#endif
    idx = (idx + i) % nVars();
    if (!theory_handler.getLogic().okToPartition(theory_handler.varToTerm(var(best)))) { unadvised_splits++; }
    return la_ok;
}

void CoreSMTSolver::updateLABest(Var v)
{
    assert(value(v) == l_Undef);
    ExVal& e = LAexacts[v];
    Lit l_v = mkLit(v, e.betterPolarity());
    buf_LABests.insert(l_v, e);
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
//    if (LABestLit != lit_Undef)
//        LABestLit = LAexacts[var(LABestLit)] < LAexacts[v] ? mkLit(v, nprops > pprops) : LABestLit;
//    else LABestLit = mkLit(v, nprops > pprops);
}

//=================================================================================================
// Garbage Collection methods:

void CoreSMTSolver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++)
        {
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++)
    {
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && reason(v) != CRef_Fake && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);
}


void CoreSMTSolver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
//    if (verbosity >= 2)
//        fprintf(stderr, "; |  Garbage collection:   %12d bytes => %12d bytes             |\n",
//               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

bool CoreSMTSolver::smtSolve( )
{
    return solve();
}

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
    for (int i = 0; ; i++)
    {
        // 2 << i == 2^(i+1)
        if ((2 << (i-1) <= split_num - splits.size()) &&
                (2 << i >= split_num - splits.size()))
        {
            // r-1(2^i) < 0 and we want absolute
            d = -(r-1/(float)(2<<(i-1))) > r-1/(float)(2<<i) ? i+1 : i;
            break;
        }
    }
    return d == decisionLevel()+assumptions.size();
}

bool CoreSMTSolver::createSplit_lookahead()
{
    // Due to the stupidness of the minisat version this gets
    // complicated
    // XXX Now that the version is updated check that this code works!
    int curr_dl0_idx = trail_lim.size() > 0 ? trail_lim[0] : trail.size();
    splits.push_c(SplitData(ca, clauses, trail, curr_dl0_idx, theory_handler, config.smt_split_format_length() == spformat_brief));
    SplitData& sp = splits.last();

    printf("; Outputing an instance:\n; ");
    Lit p = lit_Undef;
    for (int i = 0; i < decisionLevel(); i++)
    {
        vec<Lit> tmp;
        Lit l = trail[trail_lim[i]];
        if (p != l) {
            // In cases where the LA solver couldn't propagate due to
            // literal being already assigned, the literal may be
            // duplicated.  Do not report duplicates.
            tmp.push(l);
            printf("%s%d ", sign(l) ? "-" : "", var(l));
            sp.addConstraint(tmp);
        }
        p = l;
    }
    printf("\n");

    sp.updateInstance();
    assert(ok);
    return true;
}

bool CoreSMTSolver::createSplit_scatter(bool last)
{
    int curr_dl0_idx = trail_lim.size() > 0 ? trail_lim[0] : trail.size();
    assert(splits.size() == split_assumptions.size());
    splits.push_c(SplitData(ca, clauses, trail, curr_dl0_idx, theory_handler, config.smt_split_format_length() == spformat_brief));
    split_assumptions.push();
    SplitData& sp = splits.last();
    vec<Lit> constraints_negated;
    vec<Lit>& split_assumption = split_assumptions.last();
    // Add the literals on the decision levels
    for (int i = 0; i < decisionLevel(); i++) {
        vec<Lit> tmp;
        Lit l = trail[trail_lim[i]];
        tmp.push(l);
        // Add the literal
        sp.addConstraint(tmp);
        // Remember this literal in the split assumptions vector of the
        // SAT solver
        split_assumption.push(l);
        // This will be added to the SAT formula to exclude the search
        // space
        constraints_negated.push(~l);
    }
    for (int i = 0; i < split_assumptions.size()-1; i++)
    {
        vec<Lit> tmp;
        vec<Lit>& split_assumption = split_assumptions[i];
        for (int j = 0; j < split_assumption.size(); j++)
            tmp.push(~split_assumption[j]);
        sp.addConstraint(tmp);
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
    if (split_start && !split_on)
    {
        if ((split_units == spm_time && cpuTime() >= split_next) ||
                (split_units == spm_decisions && decisions >= split_next))
        {
            cancelUntil(0);
            split_start = false;
            split_on = true;
            if (split_units == spm_time) split_next = cpuTime() + split_midtune;
            if (split_units == spm_decisions) split_next = decisions + split_midtune;
        }
    }
    if (split_start && split_on)
    {
        if ((split_units == spm_time && cpuTime() >= split_next) ||
                (split_units == spm_decisions && decisions >= split_next))
        {
            cancelUntil(0);
            split_start = false;
            split_on = true;
            if (split_units == spm_time) split_next = cpuTime() + split_midtune;
            if (split_units == spm_decisions) split_next = decisions + split_midtune;
        }
    }
}

#ifdef STATISTICS
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
    os << "; Conflicts learnt.........: " << conflicts << endl;
    os << "; T-conflicts learnt.......: " << learnt_theory_conflicts << endl;
    os << "; Average learnts size.....: " << learnts_size/conflicts << endl;
    os << "; Top level literals.......: " << top_level_lits << endl;
    os << "; Search time..............: " << search_timer.getTime() << " s" << endl;
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
    if (config.sat_split_type() != spt_none)
    os << "; Ill-adviced splits.......: " << unadvised_splits << endl;
}
#endif // STATISTICS

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
