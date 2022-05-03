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

#include "ModelBuilder.h"
#include "OsmtInternalException.h"
#include "Sort.h"

#include <cmath>
#include <iostream>
#include <iomanip>
#include <algorithm>

#include "Proof.h"
#include "SystemQueries.h"
#include "ReportUtils.h"

#if defined(_MSC_VER)
#define release_assert(a) \
    do { \
    __pragma(warning(push)) \
    __pragma(warning(disable:4127)) \
        if (!(a)) {\
    __pragma(warning(pop)) \
            fprintf(stderr, "*** ASSERTION FAILURE in %s() [%s:%d]: %s\n", \
            __FUNCTION__, __FILE__, __LINE__, #a); \
            abort(); \
        } \
    } while (0)
#else
#define release_assert(a) \
    do { \
        if (!(a)) {\
            fprintf(stderr, "*** ASSERTION FAILURE in %s() [%s:%d]: %s\n", \
            __FUNCTION__, __FILE__, __LINE__, #a); \
            abort(); \
        } \
    } while (0)
#endif

namespace opensmt {
    extern bool stop;
}


//=================================================================================================
// Constructor/Destructor:

CoreSMTSolver::CoreSMTSolver(SMTConfig & c, THandler& t )
    : config           (c)
    , theory_handler   (t)
    , verbosity        (c.verbosity())
    , init             (false)
    , stop             (false)
    // Parameters: (formerly in 'SearchParams')
    , var_decay        (c.sat_var_decay())
    , clause_decay     (c.sat_clause_decay())
    , random_var_freq  (c.sat_random_var_freq())
    , luby_restart     (c.sat_luby_restart())
    , ccmin_mode       (c.sat_ccmin_mode())
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
    , learnts_size(0) , all_learnts(0)
    , learnt_theory_conflicts(0)
    , top_level_lits        (0)

    , ok                    (true)
    , conflict_frame        (0)
    , n_clauses             (0)
    , cla_inc               (1)
    , var_inc               (1)
    , watches               (WatcherDeleted(ca))
    , qhead                 (0)
    , simpDB_assigns        (-1)
    , simpDB_props          (0)
    , order_heap            (VarOrderLt(activity))
    , random_seed           (c.getRandomSeed())
    , progress_estimate     (0)
    , remove_satisfied      (true)
#ifdef PEDANTIC_DEBUG
    , max_dl_debug          (0)
    , analyze_cnt           (0)
#endif
    , conflict_budget       (-1)
    , propagation_budget    (-1)
    , asynch_interrupt      (false)
    , learnt_t_lemmata      (0)
    , perm_learnt_t_lemmata (0)
    , luby_i                (0)
    , luby_k                (1)
    , cuvti                 (false)
    , proof                 (config.produce_inter() ? new Proof(ca ) : nullptr )
#ifdef STATISTICS
    , preproc_time          (0)
    , elim_tvars            (0)
#endif
{ }

void
CoreSMTSolver::initialize( )
{
    random_seed = config.getRandomSeed();
    restart_first = config.sat_restart_first();
    restart_inc = config.sat_restart_inc();
    // Set some parameters
    skip_step = config.sat_initial_skip_step;
    skipped_calls = 0;
#ifdef STATISTICS
    preproc_time = 0;
    tsolvers_time = 0;
    ie_generated = 0;
#endif

    if (config.produce_inter() && !proof) {
        proof = std::unique_ptr<Proof>(new Proof(this->ca));
    }

    init = true;
}

CoreSMTSolver::~CoreSMTSolver()
{
#ifdef STATISTICS
    if ( config.produceStats() != 0 ) printStatistics ( config.getStatsOut( ) );
    // TODO added for convenience
    if ( config.print_stats != 0 ) printStatistics ( cerr );

    cerr << "; time used for choosing branch lit " << branchTimer.getTime() << endl;
    cerr << "; avg dec time " << branchTimer.getTime()/decisions << endl;
#endif
}

//=================================================================================================
// Minor methods:

void CoreSMTSolver::addVar(Var v)
{
    PTRef pterm = theory_handler.getTMap().varToPTRef(v);
    if (pterm == PTRef_Undef) {
        opensmt_warning("Trying to add to SAT solver a variable not bound to any pterm. Ignoring the variable!");
        return;
    }
    addVar_(v);
}

//
// Add a new var v to the solver if it does not yet exist
// It also activates the variable - turns it into decision variable - if it was not active before
//
void CoreSMTSolver::addVar_(Var v)
{
    if (v < nVars()) {
        // These are Necessary in incremental mode since previously
        // ignored vars can now reappear
        decision[v] = true;
        insertVarOrder(v);
        return;
    }
    while (v >= nVars())
        newVar(true);
}

// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var CoreSMTSolver::newVar(bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    savedPolarity.push(true);

    this->var_seen.push(false);

    // MB: Unnecessary call to insertVarOrder. This is already achieved by calling setDecisionVar above
    // insertVarOrder(v);
    assert(!decision[v] || order_heap.inHeap(v));


    // Added Lines
    // Skip undo for varTrue and varFalse
    if ( v != 0 && v != 1 )
        undo_stack.push(undo_stack_el(undo_stack_el::NEWVAR, v));

    return v;
}


bool CoreSMTSolver::addOriginalClause_(const vec<Lit> & _ps)
{
    opensmt::pair<CRef, CRef> fake;
    return addOriginalClause_(_ps, fake);
}

bool CoreSMTSolver::addOriginalClause_(const vec<Lit> & _ps, opensmt::pair<CRef, CRef> & inOutCRefs)
{
    assert(decisionLevel() == 0);
    inOutCRefs = {CRef_Undef, CRef_Undef};
    if (!isOK()) { return false; }
    bool logsProofForInterpolation = this->logsProofForInterpolation();
    vec<Lit> ps;
    _ps.copyTo(ps);
    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    std::vector<Lit> resolvedUnits;
    Lit p = lit_Undef;
    Lit ru = lit_Undef;
    int i, j;
    for (i = j = 0; i < ps.size(); i++)
    {
        if (value(ps[i]) == l_True || ps[i] == ~p)
        {
            // This original clause is already satisfied
            return true;
        }
        else if (value(ps[i]) != l_False && ps[i] != p) // Ignore duplicates and falsified literals
        {

            ps[j++] = p = ps[i];
        }
        else if (logsProofForInterpolation && value(ps[i]) == l_False && ps[i] != ru)
        {
            ru = ps[i];
            resolvedUnits.push_back(ps[i]);
        }
    }
    ps.shrink(i - j);
    if (logsProofForInterpolation) {
        vec<Lit> original;
        ps.copyTo(original);
        for(Lit l : resolvedUnits) {
            original.push(l);
        }
        CRef inputClause = ca.alloc(original);
        CRef outputClause = resolvedUnits.empty() ? inputClause :
                ps.size() == 0 ? CRef_Undef : ca.alloc(ps);
        inOutCRefs = {inputClause, outputClause};
        proof->newOriginalClause(inputClause);
        if (!resolvedUnits.empty()) {
            proof->beginChain( inputClause );
            for(Lit l : resolvedUnits) {
                Var v = var(l);
                assert(reason(v) != CRef_Undef);
                proof->addResolutionStep(reason(v), v);
            }
            proof->endChain(outputClause);
        }
    }
    if (ps.size() == 0) {
        return ok = false;
    }
    if (ps.size() == 1)
    {
        assert(value(ps[0]) == l_Undef);
        CRef reasonForAssignment = inOutCRefs.second;
        assert((logsProofForInterpolation && reasonForAssignment != CRef_Undef) || (!logsProofForInterpolation && reasonForAssignment == CRef_Undef));
        uncheckedEnqueue(ps[0], reasonForAssignment);
        CRef confl = propagate();
        ok = (confl == CRef_Undef);
        return ok;
    }
    else
    {
        CRef clauseToAttach = logsProofForInterpolation ? inOutCRefs.second : ca.alloc(ps);
        inOutCRefs.second = clauseToAttach;
        clauses.push(clauseToAttach);
        attachClause(clauseToAttach);
        // MB: TODO: remove this undo_stack
        undo_stack.push(undo_stack_el(undo_stack_el::NEWCLAUSE, clauseToAttach));
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
    if (logsProofForInterpolation()) {
        // Remove clause and derivations if ref becomes 0
        // If ref is not 0, we keep it and remove later
        if (!proof->deleted(cr)) pleaves.push(cr);
    }
    else {
        ca.free(cr);
    }
}

bool CoreSMTSolver::satisfied(const Clause& c) const
{
    for (unsigned i = 0; i < c.size(); i++)
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
        if (trail.size() > longestTrail) {
            for (auto p : trail) {
                savedPolarity[var(p)] = not sign(p);
            }
            longestTrail = trail.size();
        }
        for (int c = trail.size()-1; c >= trail_lim[level]; c--)
        {
            Var      x  = var(trail[c]);
#ifdef PEDANTIC_DEBUG
            assert(assigns[x] != l_Undef);
#endif
            assigns [x] = l_Undef;
            insertVarOrder(x);
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);

        //if ( first_model_found )
        theory_handler.backtrack(trail.size());
    }
}

void CoreSMTSolver::printClause(Clause & cl) {
    for (unsigned i = 0; i < cl.size(); ++i) {
        std::cout << cl[i] << ' ';
    }
    std::cout << '\n';
}

void CoreSMTSolver::printClause(CRef cref) {
    printClause(ca[cref]);
}

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

Var CoreSMTSolver::doRandomDecision() {
    Var next = var_Undef;
    if (branchLitRandom()) {
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++;
    }
    return next;
}

Var CoreSMTSolver::doActivityDecision() {
    Var next = var_Undef;
    while (next == var_Undef || value(next) != l_Undef || !decision[next]) {
        if (order_heap.empty()) {
            next = var_Undef;
            break;
        } else {
            next = order_heap.removeMin();
        }
    }
    return next;
}

Lit CoreSMTSolver::choosePolarity(Var next) {
    assert(next != var_Undef);
    bool sign = false;
    bool use_theory_suggested_polarity = config.use_theory_polarity_suggestion();
    if (use_theory_suggested_polarity && next != var_Undef && theory_handler.isDeclared(next)) {
        lbool suggestion = theory_handler.getSolverHandler().getPolaritySuggestion(theory_handler.varToTerm(next));
        if (suggestion != l_Undef) {
            sign = (suggestion != l_True);
            return mkLit(next, sign);
        }
    }
    sign = (savedPolarity[next] == flipState);
    return mkLit(next, sign);
}

//=================================================================================================
// Major methods:

Lit CoreSMTSolver::pickBranchLit()
{
    Var next = var_Undef;

   // Pick a variable either randomly or based on activity
    next = doRandomDecision();
    // Activity based decision
    if (next == var_Undef || value(next) != l_Undef || !decision[next])
        next = doActivityDecision();

    if (next == var_Undef) // All variables are assigned
        return lit_Undef;

    // Return the literal with the chosen polarity
    return choosePolarity(next);

}

/**
 * Compute the Glue value, as defined in Audemard & Simon:
 * Predicting Learnt Clauses Quality in Modern SAT Solvers.
 * IJCAI 2009.
 *
 * @param vector of literals each having a level in vardata
 * @return min (4, |{level(var(lit))}| \mid lit \in ps)
 */
template<class T>
uint32_t CoreSMTSolver::computeGlue(T const & ps) {
    levelsInClause.reset();
    uint32_t numLevels = 0;
    const uint32_t sz = ps.size();
    for (uint32_t i = 0; i < sz; i ++) {
        const Lit lit = ps[i];
        int level = vardata[var(lit)].level;
        if (level != 0 and not levelsInClause.contains(level)) {
            levelsInClause.insert(level);
            ++ numLevels;
            if (numLevels >= 4) {
                break;
            }
        }
    }
    return numLevels;
}

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
    bool logsProofForInterpolation = this->logsProofForInterpolation();
    assert(!logsProofForInterpolation || !proof->hasOpenChain());
    assert(confl != CRef_Undef);
    assert(cleanup.size() == 0);       // Cleanup stack must be empty
    assert(std::all_of(seen.begin(), seen.end(), [](char c) { return c == 0; })); // seen must be cleared

    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    out_btlevel = 0;

    if (logsProofForInterpolation) {
        proof->beginChain(confl);
    }

    do
    {
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt()) {
            claBumpActivity(c);
            const uint32_t newGlue = computeGlue(c);
            if (newGlue < c.getGlue()) c.setGlue(newGlue);
        }

        for (unsigned j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++)
        {
            Lit q = c[j];

            if (!seen[var(q)])
            {
                if (level(var(q)) > 0) {
                    varBumpActivity(var(q));
                    seen[var(q)] = 1;
                    // Variable propagated at current level
                    if (level(var(q)) >= decisionLevel())
                        // Increment counter for number of pivot variables left on which to resolve
                        pathC++;
                    else {
                        // Variable propagated at previous level
                        out_learnt.push(q);
                    }
                }
                else if (logsProofForInterpolation) {
                    assert(level(var(q)) == 0);
                    assert(reason(var(q)) != CRef_Undef);
                    proof->addResolutionStep(reason(var(q)), var(q));
                }
            }
        }
        // Select next clause to look at:
        while (!seen[var(trail[index--])])
            ; // Do nothing
        assert(index >= 0);
        p = trail[index+1];

        if (reason(var(p)) == CRef_Fake)
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
            theory_handler.getReason(p, r);
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
                ctr = config.sat_temporary_learn ? ca.alloc(r, {true, computeGlue(r)}) : ca.alloc(r);
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
            if (logsProofForInterpolation) {
                proof->newTheoryClause(ctr);
            }
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
        // Add resolution step only if this is not the last literal from current level
        // The last literal is not resolved! It is a part of the learnt clause
        if (logsProofForInterpolation && pathC > 0)
        {
            proof->addResolutionStep(confl, var(p));
        }
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
                for (unsigned k = 1; k < c.size(); k++)
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

    for (Lit l : analyze_toclear) {
        seen[var(l)] = 0;
    } // ('seen[]' is now cleared)
    assert(std::all_of(seen.begin(), seen.end(), [](char c) { return c == 0; }));
    // Cleanup generated lemmata
    if (not logsProofForInterpolation) {
        for (CRef cref : cleanup) {
            ca.free(cref);
        }
    }
    cleanup.clear();
//    for (int i = 0; i < out_learnt.size(); i++)
//        printf("%d ", out_learnt[i]);
//    printf("\n");
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool CoreSMTSolver::litRedundant(Lit p, uint32_t abstract_levels)
{
    // MB: TODO: figure out if this is compatible with proof tracking
    if (logsProofForInterpolation() || config.sat_minimize_conflicts <= 0 )
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
            theory_handler.getReason(p, r);
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
                ct = config.sat_temporary_learn ? ca.alloc(r, {true, computeGlue(r)}) : ca.alloc(r);
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

        for (unsigned i = 1; i < c.size(); i++)
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

    return true;
}

void CoreSMTSolver::finalizeProof(CRef finalConflict) {
    assert(this->logsProofForInterpolation());
    assert(decisionLevel() == 0);
    assert(finalConflict != CRef_Undef);
    proof->beginChain(finalConflict);

    Clause const & c = ca[finalConflict];
    for (unsigned j = 0; j < c.size(); ++j) {
        Var varToResolve = var(c[j]);
        assert(reason(varToResolve) != CRef_Undef && reason(varToResolve) != CRef_Fake);
        assert(level(varToResolve) == 0);
        CRef unitReason = reason(varToResolve);
        assert(ca[unitReason].size() == 1 && ca[unitReason][0] == ~c[j]);
        proof->addResolutionStep(unitReason, varToResolve);
    }
    proof->endChain(CRef_Undef);
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
    out_conflict.clear();
    out_conflict.push(p);

    seen[var(p)] = 1;
    if (logsProofForInterpolation()) {
        CRef assumptionUnitClause = proof->getUnitForAssumptionLiteral(~p);
        proof->beginChain(assumptionUnitClause);
    }

    for (int i = trail.size()-1; i >= 0; i--)
    {
        Var x = var(trail[i]);
        if (seen[x])
        {
            if (reason(x) == CRef_Undef)
            {
                if (assumptions_order.has(x)) {
                    out_conflict.push(~trail[i]);
                    if (logsProofForInterpolation()) {
                        assert(level(x) > 0);
                        assert(std::find(assumptions.begin(), assumptions.end(), trail[i]) != assumptions.end());
                        // Add a resolution step with unit clauses for this assumption
                        CRef assumptionUnitClause = proof->getUnitForAssumptionLiteral(trail[i]);
                        proof->addResolutionStep(assumptionUnitClause, x);
                    }
                }
            }
            else
            {
                if (reason(x) == CRef_Fake)
                {
                    cancelUntilVarTempInit(x);
                    vec<Lit> r;
                    theory_handler.getReason(trail[i], r);
                    assert(r.size() > 0);
                    assert(r[0] == trail[i]);
                    for (int j = 1; j < r.size(); j++) {
                        seen[var(r[j])] = 1;
                    }
                    cancelUntilVarTempDone();
                    if (logsProofForInterpolation()) {
                        CRef theoryClause = ca.alloc(r);
                        vardata[x].reason = theoryClause;
                        proof->newTheoryClause(theoryClause);
                        proof->addResolutionStep(theoryClause, x);
                    }
                }
                else
                {
                    Clause& c = ca[reason(x)];
                    assert(c[0] == trail[i]);
                    for (unsigned j = 1; j < c.size(); j++) {
                        seen[var(c[j])] = 1;
                    }
                    if (logsProofForInterpolation()) {
                        proof->addResolutionStep(reason(x), x);
                    }
                }
            }
            seen[x] = 0;
        }
    }
    assert(seen[var(p)] == 0);
    seen[var(p)] = 0;
    if (logsProofForInterpolation()) {
        // MB: Hopefully we have resolved away all literals including assumptions
        proof->endChain(CRef_Undef);
    }
}


void CoreSMTSolver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(from != CRef_Fake || theory_handler.getLogic().isTheoryTerm(theory_handler.varToTerm(var(p))));
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push(p);
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
            for (unsigned k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False)
                {
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                }

            // Did not find watch
            *j++ = w;
            if (value(first) == l_False) // clause is falsified
            {
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end) {
                    *j++ = *i++;
                }
                if (decisionLevel() == 0 && this->logsProofForInterpolation()) {
                    this->finalizeProof(confl);
                }
            }
            else {  // clause is unit under assignment:
                if (decisionLevel() == 0 && this->logsProofForInterpolation()) {
                    // MB: we need to log the derivation of the unit clauses at level 0, otherwise the proof
                    //     is not constructed correctly
                    proof->beginChain(cr);
                    for (unsigned k = 1; k < c.size(); k++)
                    {
                        assert(level(var(c[k])) == 0);
                        assert(reason(var(c[k])) != CRef_Fake);
                        assert(reason(var(c[k])) != CRef_Undef);
                        proof->addResolutionStep(reason(var(c[k])), var(c[k]));
                    }
                    CRef unitClause = ca.alloc(vec<Lit>{first});
                    proof->endChain(unitClause);
                    // Replace the reason for enqueing the literal with the unit clause.
                    // Necessary for correct functioning of proof logging in analyze()
                    cr = unitClause;
                }
                uncheckedEnqueue(first, cr);
            }

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

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with high glue score
    int extra = 0;
    for (i = j = 0; i < learnts.size(); i++)
    {
        Clause& c = ca[learnts[i]];
        if (c.getGlue() <= 3) {
            extra++;
        }
        if (c.getGlue() > 3 and not locked(c) and (i+extra < learnts.size() / 2)) {
            assert(c.size() > 2);
            removeClause(learnts[i]);
        } else {
            learnts[j++] = learnts[i];
        }
    }
    learnts.shrink(i - j);
    checkGarbage();
    if (logsProofForInterpolation()) {
        // Remove unused leaves
        // FIXME deal with theory lemmata when proofs will be extended to theories
        for (i = j = 0; i < pleaves.size(); i++) {
            CRef cr = pleaves[i];
            assert(ca[cr].mark() == 1);
            if (!proof->deleted(cr)) pleaves[j++] = pleaves[i];
        }
        pleaves.shrink(i - j);
    }
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
    while (static_cast<size_t>(undo_stack.size()) > new_stack_size )
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
        }
        else
        {
            throw OsmtInternalException("unknown undo operation in CoreSMTSolver" + std::to_string(op.getType()));
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
    assert( learnts.size( ) == 0 );
    // Backtrack theory solvers
    theory_handler.backtrack(trail.size());
    // Restore OK
    restoreOK( );
    assert( isOK( ) );
}

bool CoreSMTSolver::okContinue() const
{
    return not opensmt::stop;
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

bool CoreSMTSolver::vivify_if_needed()
{
    if (conflicts < next_vivify) return ok;
    next_vivify = conflicts*1.1 + 30000;
    vivif_lit_rem = 0;
    vivif_cl_rem = 0;
    uint32_t vivif_tried = 0;

    release_assert(decisionLevel() == 0);
    release_assert(ok);
    for(auto& vd: vardata) vd.reason = CRef_Undef;

    uint32_t j = 0;
    uint32_t i = 0;
    for(; i < learnts.size(); i++) {
        auto const& offs = learnts[i];
        if (!ok) {
            learnts[j++] = offs;
            continue;
        }
        release_assert(trail.size() == qhead);

        Clause& cl = ca[offs];
        if (cl.getGlue() > 2 || cl.getVivif()) {
            learnts[j++] = offs;
            continue;
        }

        vivif_tried++;
        cl.setVivif(true);
        if (vivify_one_clause(cl, offs)) {
            learnts[j++] = offs;
        } else {
            ca.free(offs);
        }
    }
    learnts.shrink(i-j);

    if (verbosity)
        std::cout << "; Vivification finished."
        << " Tried: " << vivif_tried
        << " Lit rem: " << vivif_lit_rem << std::endl;

    return ok;
}


// returns TRUE if we need to keep the clause
bool CoreSMTSolver::vivify_one_clause(Clause& cl, CRef offs)
{
    release_assert(cl.size() > 0);
    release_assert(decisionLevel() == 0);
    release_assert(ok);

    vivif_tmp_lits.resize(cl.size());
    for(uint32_t i = 0 ; i < cl.size() ; i++) vivif_tmp_lits[i] = cl[i];
    //std::random_shuffle(vivif_tmp_lits.begin(), vivif_tmp_lits.end());
    vivif_new.clear();

    newDecisionLevel();

    for(uint32_t at = 0; at < vivif_tmp_lits.size(); at++) {
        const auto l = vivif_tmp_lits[at];
        if (value(l) == l_True) {
            cancelUntil(0);
            detachClause(offs);
            return true;
        } else if (value(l) == l_False) {
            continue;
        }

        vivif_new.push_back(l);
        enqueue(~l);
        auto const confl = propagate();
        if (confl != CRef_Undef) break;
    }
    cancelUntil(0);

    if (vivif_new.size() == cl.size()) return true;
    vivif_lit_rem += cl.size() - vivif_new.size();

    assert(at > 0);
    if (vivif_new.size() == 1) {
        detachClause(offs, true);
        enqueue(vivif_new[0]);
        const auto confl = propagate();
        if (confl != CRef_Undef) {
            ok = false;
            if (verbosity) std::cout << "; vivification lead to UNSAT" << std::endl;
        }
        vivif_cl_rem++;
        return false;
    } else {
        detachClause(offs, true);
        // No need to detach&reattach, only lits 1&2 are attached.
        cl.shrink(cl.size()-vivif_new.size());
        for(uint32_t i = 0; i < vivif_new.size(); i++) cl[i] = vivif_new[i];
        attachClause(offs);
    }

    return true;
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
lbool CoreSMTSolver::search(int nof_conflicts)
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
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;

    starts++;

#ifdef STATISTICS
    const double start = cpuTime( );
#endif
    // (Incomplete) Check of Level-0 atoms

    TPropRes res = checkTheory(false, conflictC);
    if ( res == TPropRes::Unsat) {
        return zeroLevelConflictHandler();
    }

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
    if (ok) {
        if (!vivify_if_needed()) return l_False;
    }

    while (okContinue()) {
        CRef confl = propagate();
        if (confl != CRef_Undef) {
            if (conflicts > conflictsUntilFlip) {
                flipState = not flipState;
                conflictsUntilFlip += flipState ? flipIncrement / 10 : flipIncrement;
            }
            // CONFLICT
            if (conflicts % 1000 == 999) {
                uint64_t units = 0;
                if (trail_lim.size() == 0) units = trail.size();
                else units = trail_lim[0];

                if (verbosity)
                    std::cout << "; conflicts: " << std::setw(5) << std::round(conflicts/1000.0) << "K"
                    << " learnts: " << std::setw(5) << std::round(learnts.size()/1000.0) << "K"
                    << " clauses: " << std::setw(5) << std::round(clauses.size()/1000.0) << "K"
                    << " units: " << std::setw(5) << units
                    << std::endl;
            }

            conflicts++;
            conflictC++;
            if (decisionLevel() == 0) {
                return zeroLevelConflictHandler();
            }
            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);

            cancelUntil(backtrack_level);

            assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1) {
                CRef reason = CRef_Undef;
                if (logsProofForInterpolation()) {
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
                attachClause(cr);
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            learntSizeAdjust();
        } else {
            // NO CONFLICT
            if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) || !withinBudget()) {
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef;
            }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify()) {
                return zeroLevelConflictHandler();
            }
            // Two ways of reducing the clause.  The latter one seems to be working
            // better (not running proper tests since the cluster is down...)
            // if ((learnts.size()-nAssigns()) >= max_learnts)
            if (nof_learnts >= 0 and learnts.size() >= nof_learnts) {
                // Reduce the set of learnt clauses:
                reduceDB();
                nof_learnts *= nofLearntsIncrement;
            }

            // Early Pruning Call
            // Step 1: check if the current assignment is theory-consistent
            switch (checkTheory(false, conflictC)) {
                case TPropRes::Unsat:
                    return zeroLevelConflictHandler();
                case TPropRes::Propagate:
                    continue; // Theory conflict: time for bcp
                case TPropRes::Decide:
                    break; // Sat and no deductions: go ahead
                default:
                    assert( false );
            }

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()) {
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True) {
                    // Dummy decision level:
                    newDecisionLevel();
                } else if (value(p) == l_False) {
                    analyzeFinal(~p, conflict);
                    int max = 0;
                    for (Lit q : conflict) {
                        if (!sign(q)) {
                            max = assumptions_order[var(q)] > max ? assumptions_order[var(q)] : max;
                        }
                    }
                    conflict_frame = max+1;
                    return zeroLevelConflictHandler();
                } else {
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef) {
                switch (notifyConsistency()) {
                    case ConsistencyAction::BacktrackToZero:
                        cancelUntil(0);
                        break;
                    case ConsistencyAction::ReturnUndef:
                        return l_Undef;
                    case ConsistencyAction::SkipToSearchBegin:
                        continue;
                    case ConsistencyAction::NoOp:
                    default:
                        ;
                }
                // Assumptions done and the solver is in consistent state
                // New variable decision:
                decisions++;
                next = pickBranchLit();
                // Complete Call
                if ( next == lit_Undef ) {
                    TPropRes res = checkTheory(true, conflictC);

                    if ( res == TPropRes::Propagate ) {
                        continue;
                    }
                    if ( res == TPropRes::Unsat )
                    {
                        return zeroLevelConflictHandler();
                    }
                    assert( res == TPropRes::Decide );

                    // Otherwise we still have to make sure that
                    // splitting on demand did not add any new variable
                    decisions++;
                    next = pickBranchLit();
                }

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }
            
            assert(value(next) == l_Undef);
            // Increase decision level and enqueue 'next'
            assert(value(next) == l_Undef);
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
    cancelUntil(0);
    notifyEnd();
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
*/

void CoreSMTSolver::declareVarsToTheories()
{
    // First empty the solver
    theory_handler.clear();
    for (int i = 0; i < var_seen.size(); i++)
        var_seen[i] = false;

    for (int i = 0; i < trail.size(); i++)
    {
        Var v = var(trail[i]);
        if (!var_seen[v]) {
            var_seen[v] = true;
            const Logic & logic = theory_handler.getLogic();
            const PTRef term = theory_handler.varToTerm(v);
            if (logic.isTheoryTerm(term)) {
                theory_handler.declareAtom(term);
            }
        }
    }
    const Logic & logic = theory_handler.getLogic();
    top_level_lits = trail.size();
    for (int i = 0; i < clauses.size(); i++) {
        Clause & c = ca[clauses[i]];
        for (unsigned j = 0; j < c.size(); j++) {
            Var v = var(c[j]);
            if (!var_seen[v]) {
                var_seen[v] = true;
                assert(theory_handler.ptrefToVar(theory_handler.varToTerm(v)) == v);
                const PTRef term = theory_handler.varToTerm(v);
                if (logic.isTheoryTerm(term)) {
                    theory_handler.declareAtom(term);
                }
            }
        }
    }
    for (Var v = 0; v < var_seen.size(); v++) {
        if (not var_seen[v]) {
            PTRef atom = theory_handler.varToTerm(v);
            bool appearsInUf = logic.appearsInUF(atom);
            if (appearsInUf) {
                theory_handler.declareAtom(atom);
            } else {
                setDecisionVar(v, false);
            }
        }
    }
}

lbool CoreSMTSolver::solve_()
{
//    opensmt::PrintStopWatch watch("solve time", cerr);

    for (Lit l : this->assumptions) {
        this->addVar_(var(l));
    }

    // Inform theories of the variables that are actually seen by the
    // SAT solver.
    declareVarsToTheories();

    if (config.dump_only()) return l_Undef;

    random_seed = config.getRandomSeed();

    if (config.sat_dump_cnf != 0) {
        dumpCNF();
    }

    model.clear();
    conflict.clear();

    if (!ok) return l_False;

    solves++;

    double  nof_conflicts     = restart_first;
    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1)
    {
        fprintf(stderr, "; ============================[ Search Statistics ]==============================\n");
        fprintf(stderr, "; | Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        fprintf(stderr, "; |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        fprintf(stderr, "; ===============================================================================\n");
    }
    double next_printout = restart_first;

    // Search:

    if (config.dryrun())
        stop = true;
    while (status == l_Undef && !opensmt::stop && !this->stop) {
        // Print some information. At every restart for
        // standard mode or any 2^n intervarls for luby
        // restarts
        if (conflicts == 0 || conflicts >= next_printout) {
            if (config.verbosity() > 0) {
                reportf("; %9d | %8d %8d | %8.3f s | %6.3f MB\n", (int) conflicts, (int) learnts.size(), nLearnts(),
                        cpuTime(), memUsed() / 1048576.0);
                fflush(stderr);
            }
        }

        if (config.sat_use_luby_restart) {
            next_printout *= 2;
        } else {
            next_printout *= restart_inc;
        }

        // XXX
        status = search((int)nof_conflicts);
        nof_conflicts = restartNextLimit(nof_conflicts);
    }

    if (status == l_True) {
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) {
            model[i] = value(i);
        }
    } else {
        assert(opensmt::stop || status == l_False || this->stop);
    }

    // We terminate
    return status;
}

void CoreSMTSolver::clearSearch()
{
    cancelUntil(0);
//    if (first_model_found || splits.size() > 1) {
        theory_handler.backtrack(-1);
//    }
}

lbool CoreSMTSolver::zeroLevelConflictHandler() {
    ok = false;
    return l_False;
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
            // printf(" >>> RELOCING: %s%d\n", sign(p) ? "-" : "", var(p)+1);
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

void CoreSMTSolver::setAssumptions(vec<Lit> const & assumps) {
    assumptions.clear();
    assumptions_order.clear();
    assumps.copyTo(assumptions);
    int active_assumptions = 0;
    for (int i = 0; i < assumptions.size(); i++) {
        if (sign(assumptions[i])) {
            assumptions_order.insert(var(assumps[i]), active_assumptions++);
        }
    }
    if(proof) {
        proof->setCurrentAssumptionLiterals(&assumps[0], &assumps[0] + assumps.size());
    }
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

        return luby_previous.back() * lubyFactor;
    }
    // Standard restart
    return nof_conflicts * restart_inc;
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

std::ostream& operator <<(std::ostream& out, Lit l) {
    out << (sign(l) ? "-" : "") << var(l);
    return out;
}

void CoreSMTSolver::fillBooleanVars(ModelBuilder &modelBuilder) {
    Logic& logic = theory_handler.getLogic();
    for (Var v = 0; v < model.size(); ++v) {
        assert(v != var_Undef);
        PTRef atom = theory_handler.varToTerm(v);
        PTRef val;
        assert(atom != PTRef_Undef);
        assert(not logic.isNot(atom));
        if (model[v] != l_Undef) {
            val = model[v] == l_True ? logic.getTerm_true() : logic.getTerm_false();
        } else {
            // var is unassigned: use the default value
            val = logic.getDefaultValuePTRef(logic.getSort_bool());
        }
        modelBuilder.addVarValue(atom, val);
    }
}
