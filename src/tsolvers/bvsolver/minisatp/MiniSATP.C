/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

/****************************************************************************************[MiniSATP.C]
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

#include "MiniSATP.h"
#include "Sort.h"
#include <cmath>

//=================================================================================================
// Constructor/Destructor:

// Modified Line
MiniSATP::MiniSATP ( const int           i
                   , vector< Enode * > & e
                   , vector< Enode * > & d
		   , vector< Enode * > & s
		   , vector< Enode * > & v 
		   , const bool          t )
  
    // Parameters: (formerly in 'SearchParams')
  : var_decay(1 / 0.95), clause_decay(1 / 0.999), random_var_freq(0.02)
  , restart_first(100)
    // Changed from 1.5
  , restart_inc(1.1)
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // More parameters:
    //
  , expensive_ccmin  (true)
  , polarity_mode    (polarity_false)
  , verbosity        (0)

    // Statistics: (formerly in 'MiniSATPStats')
    //
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

//=================================================================================================
// Added Code

  , solver_id         ( i )
  , explanation       ( e )
  , deductions        ( d )
  , suggestions       ( s )
  , var_to_enode      ( v )
  , theory_prop       ( t )

// Added Code
//=================================================================================================

  , ok               (true)
  , cla_inc          (1)
  , var_inc          (1)
  , qhead            (0)
  , simpDB_assigns   (-1)
  , simpDB_props     (0)
  , order_heap       (VarOrderLt(activity))
  , random_seed      (91648253)
  , progress_estimate(0)
  , remove_satisfied (true)
{ 
  exp_dup.reserve( 65535 );
  var_dup.reserve( 65535 );
  exp_dup_count = 1;
  var_dup_count = 1;
  active_exp_dup = false;
  active_var_dup = false;
}


MiniSATP::~MiniSATP()
{
    for (int i = 0; i < learnts.size(); i++) free(learnts[i]);
    for (int i = 0; i < clauses.size(); i++) free(clauses[i]);
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var MiniSATP::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches   .push();          // (list for positive literal)
    watches   .push();          // (list for negative literal)
    reason    .push(NULL);
    assigns   .push(toInt(l_Undef));
    level     .push(-1);
    activity  .push(0);
    seen      .push(0);

    polarity    .push((char)sign);
    decision_var.push((char)dvar);

    insertVarOrder(v);

    // Added Lines
    undo_stack_oper.push_back( NEWVAR );
    // undo_stack_elem.push_back( (void *)&v );
    undo_stack_elem.push_back( reinterpret_cast< void * >( v ) );

    return v;
}


// Modified line
// bool MiniSATP::addClause(vec<Lit>& ps, Enode * e)
bool MiniSATP::addClause(vec<Lit>& psin, Enode * e)
{
    assert( decisionLevel() == 0 );
    assert( ok );

    // Added Lines
    vec< Lit > ps;
    psin.copyTo( ps );

    if (!ok)
      return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
    {
      if (value(ps[i]) == l_True || ps[i] == ~p)
	return true;
      else if (value(ps[i]) != l_False && ps[i] != p)
	ps[j++] = p = ps[i];
    }
    ps.shrink(i - j);

//=================================================================================================
// Modified Code

    assert( psin.size( ) == 1 || ps.size() > 0 );

    //
    // This case happens only when deductions are enabled
    //
    if (ps.size() == 0)
    {
      Clause * confl = Clause_new( psin );
      if ( confl == NULL ) return ok = true;
      initExpDup( );
      explanation.push_back( e );
      storeExpDup( e );
      fillExplanation( confl );
      doneExpDup( );
      assert( !explanation.empty( ) );
      return ok = false;
    }

    if (ps.size() == 1)
    {
      assert(value(ps[0]) == l_Undef);
      uncheckedEnqueue(ps[0]);
      /*
      const Var v = var(ps[0]);
      if ( var_to_enode.size( ) <= v )
	var_to_enode.resize( v + 1, NULL );
      var_to_enode[ v ] = e;
      */
      /*
      if ( e != NULL && seen_in_conflict.insert( e->getId( ) ).second )
	explanation.push_back( e );
      */
      // undo_stack_oper.push_back( NEWUNIT );
      // undo_stack_elem.push_back( (void *)v );

#define LAZY_PROPAGATION 0
#if LAZY_PROPAGATION
#else
      // Modified Line
      // return ok = (propagate() == NULL);
#if LIMIT_DEDUCTIONS
      deductions_done_in_call = 0;
#endif
      Clause * confl = propagate( theory_prop );
      if ( confl == NULL ) return ok = true;
      initExpDup( );
      fillExplanation( confl );
      doneExpDup( );
      assert( !explanation.empty( ) );
      return ok = false;
#endif

// Modified Code
//=================================================================================================

    }
    else
    {
      Clause* c = Clause_new(ps, false);
      clauses.push(c);
      attachClause(*c);

      // Added Lines
      undo_stack_oper.push_back( NEWCLAUSE );
      undo_stack_elem.push_back( (void *)c );
    }

    return true;
}

void MiniSATP::attachClause(Clause& c) 
{
    assert(c.size() > 1);
    watches[toInt(~c[0])].push(&c);
    watches[toInt(~c[1])].push(&c);
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); 
}


void MiniSATP::detachClause(Clause& c) {
    assert(c.size() > 1);
    assert(find(watches[toInt(~c[0])], &c));
    assert(find(watches[toInt(~c[1])], &c));
    remove(watches[toInt(~c[0])], &c);
    remove(watches[toInt(~c[1])], &c);
    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }

// Modified Lines
// void MiniSATP::removeClause(Clause& c) 
// {
void MiniSATP::removeClause(Clause& c) 
{
    // Remove clause from reasons
    // 
    for ( int i = 0 ; i < c.size( ) ; i ++ )
    {
      const Var v = var(c[i]);
      if ( reason[ v ] == &c )
	reason[ v ] = NULL;
    }
    detachClause(c);
    removed.push( &c );
}


bool MiniSATP::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void MiniSATP::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var     x  = var(trail[c]);
            assigns[x] = toInt(l_Undef);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit MiniSATP::pickBranchLit(int polarity_mode, double random_var_freq)
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (toLbool(assigns[next]) == l_Undef && decision_var[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || toLbool(assigns[next]) != l_Undef || !decision_var[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    bool sign = false;
    switch (polarity_mode){
    case polarity_true:  sign = false; break;
    case polarity_false: sign = true;  break;
    case polarity_user:  sign = polarity[next]; break;
    case polarity_rnd:   sign = irand(random_seed, 2); break;
    default: assert(false); }

    return next == var_Undef ? lit_Undef : Lit(next, sign);
}


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
void MiniSATP::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    out_btlevel = 0;

    do{
        assert(confl != NULL);          // (otherwise should be UIP)
        Clause& c = *confl;

	// Added Line
	fillExplanation( confl );

        if (c.learnt())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level[var(q)] > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level[var(q)] >= decisionLevel())
                    pathC++;
                else{
                    out_learnt.push(q);
                    if (level[var(q)] > out_btlevel)
                        out_btlevel = level[var(q)];
                }
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])])
	  ; // Do nothing
        p     = trail[index+1];
        confl = reason[var(p)];
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    if (expensive_ccmin){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason[var(out_learnt[i])] == NULL || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
    }else{
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
    else{
        int max_i = 1;
        for (int i = 2; i < out_learnt.size(); i++)
            if (level[var(out_learnt[i])] > level[var(out_learnt[max_i])])
                max_i = i;
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level[var(p)];
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


//=================================================================================================
// Added Code

void MiniSATP::fillExplanation(Clause* confl)
{
  assert( confl != NULL );
  // Initializes cache for visited variables
  initVarDup( );

  vector< Clause * > unprocessed_clauses;
  unprocessed_clauses.push_back( confl );

  while( !unprocessed_clauses.empty( ) )
  {
    Clause & c = *unprocessed_clauses.back( );
    unprocessed_clauses.pop_back( );
    //
    // First of all, add reasons for conflict clause
    //
    for ( int j = 0 ; j < c.size() ; j++ )
    {
      Lit p = c[j];
      const Var v = var(p);
      if ( isVarDup( v ) )
	continue;

      storeVarDup( v );

      assert( reason.size( ) > v );

      //
      // If propagated
      //
      if ( reason[v] )
      {
	unprocessed_clauses.push_back( reason[v] );
      }
      //
      // Otherwise is activation var
      //
      else
      {
#if 0
	Map( Var, Enode * )::iterator it = var_to_enode.find( v );
	if ( it != var_to_enode.end( ) && 
	     seen_in_conflict.insert( it->second->getId( ) ).second )
#else
	assert( (int)var_to_enode.size( ) > v );
	Enode * e = var_to_enode[ v ];
	if ( e != NULL && !isExpDup( e ) )
#endif
	{
	  explanation.push_back( e );
	  storeExpDup( e );
	}
      }
    }
  } 

  doneVarDup( );
}

// Added Code
//=================================================================================================


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool MiniSATP::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason[var(analyze_stack.last())] != NULL);
        Clause& c = *reason[var(analyze_stack.last())]; analyze_stack.pop();

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
void MiniSATP::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
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


void MiniSATP::uncheckedEnqueue(Lit p, Clause* from)
{
    assert(value(p) == l_Undef);
    assigns [var(p)] = toInt(lbool(!sign(p)));  // <<== abstract but not uttermost effecient
    level   [var(p)] = decisionLevel();
    reason  [var(p)] = from;
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
Clause* MiniSATP::propagate(const bool deduce)
{
    Clause* confl     = NULL;
    int     num_props = 0;

    while (qhead < trail.size()){
        Lit             p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
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

                // Did not find watch -- clause is unit under assignment:
                *j++ = &c;
                if (value(first) == l_False){
                    confl = &c;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                }
		else
		{
		  uncheckedEnqueue(first, &c);

//=================================================================================================
// Added Code

		  assert( (int)var_to_enode.size( ) > var( first ) );
		  if ( deduce && var_to_enode[ var( first ) ] != NULL )
		  {
		    Enode * e = var_to_enode[ var( first ) ];
		    if ( !e->hasPolarity( ) && !e->isDeduced( ) )
		    {
		      e->setDeduced( sign( first ), solver_id );
		      deductions.push_back( e );
		    }
		  }

// Added Code
//=================================================================================================

		}
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
void MiniSATP::reduceDB()
{
    // Added Line
    // Prevent any clause removal for now
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
}


void MiniSATP::removeSatisfied(vec<Clause*>& cs)
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
bool MiniSATP::simplify()
{
    remove_satisfied = false;
    assert(decisionLevel() == 0);

    // Modified Lines
    // if (!ok || propagate() != NULL)
        // return ok = false;
    if (!ok) return false;
    Clause * confl = propagate( );
    if ( confl != NULL )
    {
      fillExplanation( confl );
      return ok = false;
    }

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);

    // Remove fixed variables from the variable heap:
    order_heap.filter(VarFilter(*this));

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

//=================================================================================================
// Added Code

void
MiniSATP::pushBacktrackPoint( ) 
{ 
  //
  // Save undo stack size
  //
  assert( undo_stack_oper.size( ) == undo_stack_elem.size( ) );
  undo_stack_size.push_back( undo_stack_oper.size( ) );
  undo_trail_size.push_back( trail.size( ) );
}

void
MiniSATP::popBacktrackPoint ( ) 
{ 
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
    }
    else if ( op == NEWUNIT )
    {
    }
    else if ( op == NEWCLAUSE )
    {
      Clause * c = (Clause *)undo_stack_elem.back( );
      assert( clauses.last( ) == c );
      // assert( c->id + 1 == (int)clause_id_to_enode.size( ) );
      clauses.pop( );
      removeClause( *c );
      // clause_id_to_enode.pop_back( );
    }
    else
    {
      opensmt_error2( "unknown undo operation in BitBlaster", op );
    }

    undo_stack_oper.pop_back( );
    undo_stack_elem.pop_back( );
  }

  while( learnts.size( ) > 0 )
  {
    Clause * c = learnts.last( );
    learnts.pop( );
    removeClause( *c );
  }

  while( removed.size( ) > 0 )
  {
    Clause * c = removed.last( );
    removed.pop( );
    free( c ); 
  }
    
  assert( undo_stack_elem.size( ) == undo_stack_oper.size( ) );
  assert( learnts.size( ) == 0 );
  assert( removed.size( ) == 0 );
}

// Added Code
//=================================================================================================

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
lbool MiniSATP::search(int nof_conflicts, int nof_learnts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;

    starts++;

    bool first = true;

    for (;;){
        Clause* confl = propagate();
        if (confl != NULL){
            // CONFLICT
            conflicts++; conflictC++;

            if (decisionLevel() == 0) 
	    {
	      // Added Lines
	      fillExplanation(confl);
	      return l_False;
	    }

            first = false;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);
            assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                Clause* c = Clause_new(learnt_clause, true);
                learnts.push(c);
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
            if (decisionLevel() == 0 && !simplify())
	    {
                return l_False;
	    }

            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

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

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit(polarity_mode, random_var_freq);

                if (next == lit_Undef)
		{
		    // Added Line
		    // Clear explanation vector if satisfiable
		    explanation.clear( );

                    // Model found:
                    return l_True;
		}
            }

            // Increase decision level and enqueue 'next'
            assert(value(next) == l_Undef);
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double MiniSATP::progressEstimate() const
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


bool MiniSATP::solve(const vec<Lit>& assumps)
{
    // Added Line
    initExpDup( );

    model.clear();
    conflict.clear();

    if (!ok) { 
      // Added Line
      doneExpDup( );

      return false;
    }

    assumps.copyTo(assumptions);

    double  nof_conflicts = restart_first;
    double  nof_learnts   = nClauses() * learntsize_factor;
    lbool   status        = l_Undef;

    if (verbosity >= 1){
        reportf("============================[ Search Statistics ]==============================\n");
        reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        reportf("===============================================================================\n");
    }

    // Search:
    while (status == l_Undef){
        if (verbosity >= 1)
            reportf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)conflicts, order_heap.size(), nClauses(), (int)clauses_literals, (int)nof_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progress_estimate*100), fflush(stdout);
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts *= restart_inc;
        nof_learnts   *= learntsize_inc;
    }

    if (verbosity >= 1)
        reportf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
#ifndef NDEBUG
        verifyModel();
#endif
    }else{
        assert(status == l_False);
        if (conflict.size() == 0)
            ok = false;
    }

    cancelUntil(0);

    // cerr << "SOLVE: Memory after: " << memUsed( ) / 1024.0 / 1024.0 << endl;
    
    // Added Line
    doneExpDup( );
    assert( status == l_True || !explanation.empty( ) );

    return status == l_True;
}

//=================================================================================================
// Debug methods:


void MiniSATP::verifyModel()
{
    bool failed = false;
    for (int i = 0; i < clauses.size(); i++){
        assert(clauses[i]->mark() == 0);
        Clause& c = *clauses[i];
        for (int j = 0; j < c.size(); j++)
            if (modelValue(c[j]) == l_True)
                goto next;

        reportf("unsatisfied clause: ");
        printClause(*clauses[i]);
        reportf("\n");
        failed = true;
    next:;
    }

    assert(!failed);

    // Modified Line
    //reportf("Verified %d original clauses.\n", clauses.size());
}


void MiniSATP::checkLiteralCount()
{
    // Check that sizes are calculated correctly:
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (clauses[i]->mark() == 0)
            cnt += clauses[i]->size();

    if ((int)clauses_literals != cnt){
        fprintf(stderr, "literal count: %d, real value = %d\n", (int)clauses_literals, cnt);
        assert((int)clauses_literals == cnt);
    }
}
