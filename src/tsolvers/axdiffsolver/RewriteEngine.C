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

#include "RewriteEngine.h"
#include <algorithm>

#define PRINT_EXPL_DOT 0      // Dump explanation graphs in dotty format
#define LESS_R1        1

bool RewriteEngine::lessThan( Enode * l, Enode * r )
{
  assert( l->isVar( ) );
  assert( r->isVar( ) );

#ifdef PRODUCE_PROOF
  if ( config.produce_inter == 0 )
    return l->getId( ) < r->getId( );

  // Custom lt has precedence
  Pair( Enode * ) p = make_pair( l, r );
  if ( custom_lt.find( p ) != custom_lt.end( ) )
    return true;

  // Interpolating version
  const ipartitions_t & l_parts = l->getIPartitions( );
  const ipartitions_t & r_parts = r->getIPartitions( );
  assert( l_parts != 0 );
  assert( r_parts != 0 );
  assert( (l_parts & r_parts) != 0 );   // if it's 0 means AB-mixed
  // Same partition, choose by id
  if ( l_parts == r_parts )
    return l->getId( ) < r->getId( );
  if ( isABcommon( l ) )
    return true;
  assert ( isABcommon( r ) );
  return false;
#else
  // Non interpolating version
  return l->getId( ) < r->getId( );
#endif
}

bool RewriteEngine::greaterThan( Enode * l, Enode * r )
{
  return lessThan( r, l );
}

//
// Orient a rule. Returns 
// 0 if orientation was done
// 1 if badly orientable rule found
// 2 if badly orientable interpolating rule found
// 3 if badly orientable to be rotated
// 4 if invariant breaking rule
//
int RewriteEngine::orient( Enode **l, Enode **r )
{
  bool swap = false;
  // Two variables in wrong order
  if ( (*l)->isVar( ) 
    && (*r)->isVar( )
    && lessThan( *l, *r ) )
  {
    swap = true;
  }
  else if ( (*r)->isSelect( ) )
  {
    assert( (*l)->isVar( ) );
    swap = true;
  }
  else if ( (*l)->isStore( ) )
  {
    assert( (*r)->isVar( ) );
    swap = true;
  }
  else if ( (*r)->isDiff( ) )
  {
    assert( (*l)->isVar( ) );
    swap = true;
  }

  if ( swap )
  {
    Enode * tmp = (*l);
    (*l) = (*r);
    (*r) = tmp;
  }
  //
  // Check if badly orientable equality
  // Cases 
  // rd( c, i ) = d
  // diff( a, b ) = d
  // where lhs is AB-common, rhs is A-local/B-local
  // This cases should never happen because of 
  // preprocessing
  //
  if ( (*r)->isStore( ) )
  {
    Enode * inner_var = (*r);
    while ( !inner_var->isVar( ) )
      inner_var = inner_var->get1st( );

#if PRODUCE_PROOF
    if ( config.produce_inter != 0 )
    {
      const bool cond1 = isABcommon( *l ) && ( isAlocal( *r ) || isBlocal( *r ) );
      const bool cond2 = !greaterThan( (*l), inner_var );

      if ( cond1 && cond2 ) return 3; // Badly orientable to be rotated
      else if ( cond1 ) return 2;     // Badly orientable not to be rotated
      else if ( cond2 ) return 1;     // To be rotated
    }
    else
#endif
    if ( !greaterThan( (*l), inner_var ) )
      return 1;
  }

  return 0;
}

void RewriteEngine::check( const bool index_total )
{
#if SPLIT_ON_DEMAND
  candidate = NULL;
  nof_idxs  = 0;
#endif

  (void)index_total;
  assert( status == l_Undef );

  // To avoid redundant explanations
  seen_in_expl.clear( );
  // Clear reduced diffs
  reduced_diffs.clear( );

  // Save current state
  pushBacktrackPoint( );

  if ( config.verbosity > 2 )
    cerr << "# Loading ELEM equalities (and doing completion)" << endl;

  // Load accumulated Equalities
  for ( size_t i = 0 
      ; i < select_equalities_to_add.size( ) && status == l_Undef
      ; i ++ )
  {
    // Can turn status to l_False
    addGroundRule( select_equalities_to_add[ i ]->get1st( )
                 , select_equalities_to_add[ i ]->get2nd( )
                 , select_equalities_to_add[ i ] );
  }

  if ( config.verbosity > 2 )
    cerr << "# Loading ARRAY equalities (and doing completion)" << endl;

  for ( size_t i = 0 
      ; i < store_equalities_to_add.size( ) && status == l_Undef
      ; i ++ )
  {
    // Can turn status to l_False
    addGroundRule( store_equalities_to_add[ i ]->get1st( )
                 , store_equalities_to_add[ i ]->get2nd( )
                 , store_equalities_to_add[ i ] );
#if OUTSPLIT
    if ( new_idx )
    {
      goto out_split;
      new_idx = false;
    }
#endif
  }

  assert( status == l_Undef || status == l_False );

#if REDUCE_TO_EUF

  vector< Enode * > eqs_to_unset;
  vector< Enode * > eqs_to_deassert;

  bool res = true;

  egraph.extPushBacktrackPoint( );

  /*
   * NO NEED ! REMEMBER EQ-LAYERING ...
   *
  // Send all negated equalities to EUF
  for ( size_t i = 0 ; i < neq_list.size( ) ; i ++ )
    egraph.extAssertLit( neq_list[ i ] );
  */

  // Now send all equalities within eqs_to_antec to EUF
  for ( map< Enode *, vector< Enode * > >::iterator it = eqs_to_antec.begin( )
      ; it != eqs_to_antec.end( ) && res
      ; it ++ )
  {
    Enode * eq = it->first;

    if ( !eq->hasPolarity( ) )
    {
      eq->setPolarity( l_True );
      assert( eq->hasPolarity( ) );
      eqs_to_unset.push_back( eq );
    }

    // cerr << "ASSERTING IN EQ: " << eq << endl;

    res = egraph.extAssertLit( eq );
  }

  // cerr << "RES IS: " << res << endl;
  
  bool deduced = false;

  vector< Enode * > saved_deds; 
  // if ( res )
    // deduced = egraph.deduceMore( saved_deds );

  egraph.extPopBacktrackPoint( );

  if ( !res )
  {
    /*
    cerr << "EXPLANATION IS: " << endl;
    // Send all negated equalities to EUF
    for ( size_t i = 0 ; i < explanation.size( ) ; i ++ )
      cerr << (explanation[ i ]->getPolarity( ) == l_False ? " !":"  " ) << explanation[ i ] << endl;
    */

    // minimizeExplanation( );

    // cerr << "MINIMIZED EXPLANATION IS: " << endl;
    // Send all negated equalities to EUF
    // for ( size_t i = 0 ; i < explanation.size( ) ; i ++ )
      // cerr << " " << explanation[ i ] << endl;

    vector< Enode * > tmp_explanation;
    tmp_explanation.swap( explanation );
    map< Enode *, vector< Enode * > >::iterator it;
    for ( size_t i = 0 ; i < tmp_explanation.size( ) ; i ++ )
    {
      it = eqs_to_antec.find( tmp_explanation[ i ] );
      if ( it != eqs_to_antec.end( ) )
      {
	explanation.insert( explanation.end( )
	                  , (it->second).begin( )
			  , (it->second).end( ) );
      }
      else
      {
	explanation.push_back( tmp_explanation[ i ] );
      }
    }
    sort( explanation.begin( ), explanation.end( ) );
    vector< Enode * >::iterator new_end = unique( explanation.begin( ), explanation.end( ) );
    explanation.erase( new_end, explanation.end( ) );

    /*
    cerr << "FINAL EXPLANATION IS: " << endl;
    // Send all negated equalities to EUF
    for ( size_t i = 0 ; i < explanation.size( ) ; i ++ )
      cerr << (explanation[ i ]->getPolarity( ) == l_False ? " !":"  " ) << explanation[ i ] << endl;
    */

    status = l_False;
  }
  else
  {
    if ( deduced )
    {
      deductions.insert( deductions.end( )
	               , saved_deds.begin( )
		       , saved_deds.end( ) );
    }
#if SPLIT_ON_DEMAND
    // const bool deduced = false; 
    else if ( index_total 
           && candidate != NULL )
    {
      cerr << "GENERATED CANDIDATE: " << candidate << endl;
      egraph.splitOnDemand( candidate, id );
    }
#endif
    status = l_True;
  }

  // Reset custom polarities
  while ( !eqs_to_unset.empty( ) )
  {
    Enode * eq = eqs_to_unset.back( );
    eqs_to_unset.pop_back( );
    eq->resetPolarity( );
  }

  // Clear eqs_to_antec
  eqs_to_antec.clear( );

#else // REDUCE_TO_EUF

#ifdef PRODUCE_PROOF
  // Call interpolating version of check
  if ( config.produce_inter != 0 )
  {
    computeIdxEqClasses( );
    bo_to_skip.clear( );
    fixBadSelect( );
    fixBadlyOrientable( );
    iCheck( 0 );
    if ( status == l_False )
    {
      explanation.clear( );
      explanation.insert( explanation.end( )
	                , acc_expl.begin( )
			, acc_expl.end( ) );
      // Remove duplicates
      sort( explanation.begin( ), explanation.end( ) );
      vector< Enode * >::iterator new_end = unique( explanation.begin( ), explanation.end( ) );
      explanation.erase( new_end, explanation.end( ) );
    }

    if ( status == l_False )
    {
      assert( checkInterpolant( interpolant ) );

      // Undo definitions
      for( int i = def_stack.size( ) - 1 ; i >= 0 ; i -- )
      {
	Enode * r_prime = def_stack[ i ];
	assert( definitions.find( r_prime ) != definitions.end( ) );
	Enode * l = definitions[ r_prime ];
	assert( isABcommon( l ) );
	egraph.initDupMap1( );
	egraph.storeDupMap1( r_prime, l );
	interpolant = substitute( interpolant );
	egraph.doneDupMap1( );
      }

      assert( checkInterpolant( interpolant ) );

      if ( config.verbosity > 3 )
	cerr << "# Interpolant: " << interpolant << endl;
    }
  }
  else
  {
    check_( ground_rules, neq_list );
  }
#else
  check_( ground_rules, neq_list );
#endif

#if OUTSPLIT
out_split:
  status = l_True;
#endif

#endif // REDUCE_TO_EUF

  assert( status == l_False || status == l_True );
  assert( status == l_True || !explanation.empty( ) );

  popBacktrackPoint( );
}

#if REDUCE_TO_EUF
void RewriteEngine::minimizeExplanation( )
{
  assert( !explanation.empty( ) );
  vector< Enode * > orig_expl;
  vector< bool > redundant;
  // Save aside explanation
  orig_expl.swap( explanation );
  redundant.resize( orig_expl.size( ), false );
  vector< Enode * > non_redundant;

  size_t candidate = 0;

  while ( candidate < orig_expl.size( ) )
  {
    // Save state
    egraph.extPushBacktrackPoint( );

    cerr << "Check if: " << orig_expl[ candidate ] << " is red ... " << endl;

    bool res = true;
    // Load equalities
    for ( size_t i = 0 ; i < orig_expl.size( ) && res ; i ++ )
    {
      // skip candidate
      if ( candidate == i ) continue;
      // skip already proven redundant
      if ( redundant[ i ] ) continue;
      cerr << "   loading: " << orig_expl[ i ] << endl;
      res = egraph.extAssertLit( orig_expl[ i ] );
    }

    // Accumulate non redundant
    if ( res )
      non_redundant.push_back( orig_expl[ candidate ] );
    // Redundant if still unsat
    else
    {
      redundant[ candidate ] = true;
      explanation.clear( );
    }

    cerr << (res?"not redundant":"redundant") << endl;
    
    // Save state
    egraph.extPopBacktrackPoint( );
    // Next candidate, if any
    candidate ++;
  }

  explanation.swap( non_redundant );
  assert( !explanation.empty( ) );
}
#endif

// 
// Actual check on the current set of rules
//
void RewriteEngine::check_( ground_rules_t & g_rules
                           , vector< Enode * > & n_list )
{
  while( status == l_Undef )
  {
    // Exhaustively apply C3, which is not considered in addAndComplete
    applyC3( g_rules );

    // Apply reduction
    const bool reduced = reduction( g_rules );

    // Continue to completion again if some reduction was done
    if ( reduced ) continue;

    // Check failure conditions; turns status into l_False or l_True
    failure( g_rules, n_list );

    assert( status == l_True || status == l_False );
  }
}

//
// Iterates over the rule database and
// look for applications of C3 rule.
// Accumulates all the pairs, compute
// critical pairs and restart until 
// saturation
//
void RewriteEngine::applyC3( ground_rules_t & g_rules )
{
  if ( config.verbosity > 3 )
  {
    cerr << "# Applications of C3 ..." << endl;
  }

  vector< RewriteRule * > postponed;

  bool saturated = false;
  while ( !saturated )
  {
    saturated = true;
    //
    // Iterates over the ground rules to
    // see if there is anything to be done
    //
    for ( ground_rules_t::iterator it = g_rules.begin( )
	; it != g_rules.end( )
	; it ++ )
    {
      RewriteRule * r_i = it->second;

      if ( !r_i->lhs->isSelect( ) )
	continue;

      Enode * a = r_i->lhs->get1st( );

      vector< RewriteRule * > r_antec;
      vector< Enode * > e_antec;
      r_antec.push_back( r_i );
      Enode * rew_a = rewriteGround( g_rules, a, r_antec, e_antec );

      if ( a != rew_a )
      {
	// Postpone Case 3
	postponed.push_back( r_i );
      }
    }

    while( !postponed.empty( ) )
    {
      RewriteRule * r_i = postponed.back( );
      postponed.pop_back( );

      vector< RewriteRule * > r_antec;
      vector< Enode * > e_antec;
      r_antec.push_back( r_i );

      Enode * a = r_i->lhs->get1st( );
      Enode * rew_a = rewriteGround( g_rules, a, r_antec, e_antec );

      assert( a != rew_a );

      Enode * rew_lhs = egraph.mkSelect( rew_a, r_i->lhs->get2nd( ) );

      Enode * rew_lhs_p = rewrite( g_rules, rew_lhs, r_antec, e_antec );
      Enode * rew_rhs   = rewrite( g_rules, r_i->rhs, r_antec, e_antec );

#ifdef PRODUCE_PROOF
      assert( config.produce_inter == 0 
	   || rew_lhs_p->getIPartitions( ) != 0 );
      assert( config.produce_inter == 0
	   || rew_lhs->getIPartitions( ) != 0 );
#endif

      if ( rew_rhs != rew_lhs_p )
      {
	if ( config.verbosity > 3 )
	{
	  cerr << "# Case 3 applies for" << endl
	       << "#  " << rew_lhs_p << " <-- " 
	                << rew_lhs << " <--" 
			<< r_i << endl;
	}

	addGroundRule( rew_lhs_p, rew_rhs, NULL, g_rules, r_antec, e_antec );

	disableGroundRule( g_rules, r_i );
	saturated = false;
      }
    }
  }
}

bool RewriteEngine::reduction( ground_rules_t & g_rules )
{
  if ( config.verbosity > 3 )
  {
    cerr << "# Applications of R2 and R3 ..." << endl;
  }
  //
  // Condition (R1) is implicit 
  //
  //
  // Condition (R2)
  //
  vector< RewriteRule * > rules_to_process;
  bool reduced = false;
  for ( ground_rules_t::iterator it = g_rules.begin( )
      ; it != g_rules.end( )
      ; it ++ )
  {
    RewriteRule * rule = it->second;

    if ( rule->lhs->getRetSort( ) != egraph.getSortArray( ) )
      continue;

    if ( !rule->rhs->isStore( ) )
      continue;

    rules_to_process.push_back( rule );
  }

  while ( !rules_to_process.empty( ) )
  {
    RewriteRule * rule = rules_to_process.back( );
    rules_to_process.pop_back( );

    vector< RewriteRule * > r_antec;
    vector< Enode * > e_antec;
    // Nothing should happen, but just to make sure ...
    Enode * nf = rewrite( g_rules, rule->rhs, r_antec, e_antec );

    r_antec.push_back( rule );

    Enode * b = nf;
    while ( b->isStore( ) )
      b = b->get1st( );

    set< Enode * > indexes_to_remove;
    vector< Enode * > indexes;
    vector< Enode * > elements;
    while ( nf->isStore( ) )
    {
      // If rd(b,i) ~ e
      Enode * e = nf->get3rd( );
      Enode * i = nf->get2nd( );
      indexes.push_back( i );
      elements.push_back( e );
      Enode * rd = egraph.mkSelect( b, getRoot( i ) );
      vector< RewriteRule * > tmp1;
      vector< Enode * > tmp2;
      rd = rewrite( g_rules, rd, tmp1, tmp2 ); 
      e  = rewrite( g_rules, e , tmp1, tmp2 );
      if ( rd == e )
	indexes_to_remove.insert( i );
      nf = nf->get1st( );
    }

    if ( !indexes_to_remove.empty( ) )
    {
      Enode * new_rhs = nf;
      while ( !indexes.empty( ) )
      {
	Enode * i = indexes.back( );
	Enode * e = elements.back( );
	indexes.pop_back( );
	elements.pop_back( );

	// Not adding this
	if ( indexes_to_remove.find( i ) != indexes_to_remove.end( ) )
	  continue;

	Enode * old_rhs = new_rhs;
	new_rhs = egraph.mkStore( old_rhs, i, e );
      }
      reduced = true;
      disableGroundRule( g_rules, rule );

      addGroundRule( rule->lhs
	           , new_rhs
		   , NULL
		   , g_rules
		   , r_antec
		   , e_antec ); 
    }
  }
  //
  // Condition (R3)
  //
  // Scan through the diff list
  //
  for ( size_t i = 0 ; i < diff_list.size( ) ; i ++ )
  {
#if 1
    break;
#endif
    // Prevents loops
    if ( reduced_diffs.find( i ) != reduced_diffs.end( ) )
      continue;

    Enode * index = diff_list[ i ]->rhs;
    vector< Enode * > matches;
    set< Enode * > seen;

    Enode * a = diff_list[ i ]->lhs->get1st( );
    Enode * b = diff_list[ i ]->lhs->get2nd( );
    assert( a->isVar( ) );
    assert( b->isVar( ) );
    assert( a != b );

    // Make it such that a > b
    if ( lessThan( a, b ) )
    {
      Enode * tmp = a;
      a = b;
      b = tmp;
    }

    vector< RewriteRule * > r_antec;
    vector< Enode * > e_antec;

#ifdef PRODUCE_PROOF
    // Internal rules don't need explanations
    if ( config.produce_inter == 0
      || internals.find( diff_list[ i ] ) ==
         internals.end( ) )      
#endif
    /*
    egraph.explain( diff_list[ i ]->lhs
	          , diff_list[ i ]->rhs
		  , e_antec );
    */
    indexExplain( diff_list[ i ]->lhs
	        , diff_list[ i ]->rhs
		, e_antec );

    Enode * ra = egraph.mkSelect( a, index );
    Enode * rb = egraph.mkSelect( b, index );

    Enode * rew_ra = rewrite( g_rules, ra, r_antec, e_antec );
    Enode * rew_rb = rewrite( g_rules, rb, r_antec, e_antec );

    if ( rew_ra == rew_rb )
    {
      addGroundRule( a, b, NULL, g_rules, r_antec, e_antec );
      // Prevents loops
      reduced_diffs.insert( i );
      reduced = true;
    }
  }

  if ( config.verbosity > 3 )
  {
    if ( reduced )
      cerr << "#  Something was reduced" << endl;
    else
      cerr << "#  Nothing was reduced" << endl;
  }
  
  return reduced;
}

void RewriteEngine::failure( ground_rules_t & g_rules
                           , vector< Enode * > & n_list )
{
  if ( config.verbosity > 3 )
    cerr << "#  Checking failure" << endl;

  //
  // Condition (U1)
  //
  for ( size_t i = 0 ; i < n_list.size( ) ; i ++ )
  {
    Enode * lhs = n_list[ i ]->get1st( );
    Enode * rhs = n_list[ i ]->get2nd( );
    vector< RewriteRule * > r_antec;
    vector< Enode * > e_antec;
    assert( lhs->isVar( ) );
    assert( rhs->isVar( ) );
    lhs = rewrite( g_rules, lhs, r_antec, e_antec );
    rhs = rewrite( g_rules, rhs, r_antec, e_antec );

    if ( lhs == rhs )
    {
      if ( config.verbosity > 3 )
	cerr << "#  Failure found" << endl;

#ifdef PRODUCE_PROOF
      assert( config.produce_inter != 0 
	   || n_list[ i ]->hasPolarity( ) );
#endif

      // Neq is in conflict
      if ( seen_in_expl.insert( n_list[ i ] ).second 
	&& n_list[ i ]->hasPolarity( ) )
      {
	assert( n_list[ i ]->getPolarity( ) == l_False );
	explanation.push_back( n_list[ i ] );
      }
#ifdef PRODUCE_PROOF

      if ( config.produce_inter != 0 )
      {
	Enode * neq = NULL;
	if ( (  turn_A && isBlocal( n_list[ i ] ) )
	  || ( !turn_A && isAlocal( n_list[ i ] ) ) )
	{
	  neq = n_list[ i ];
	}
	interpolate( neq, r_antec );
      }
#endif

      // Compute conflict
      explain( r_antec );

      // Set status false
      status = l_False;

      return;
    }
  } 
  //
  // Condition (U2)
  //
  for ( size_t i = 0 ; i + 1 < diff_list.size( ) ; i ++ )
  {
    for ( size_t j = i + 1 ; j < diff_list.size( ) ; j ++ )
    {
      Enode * diff   = diff_list[ i ]->lhs;
      Enode * idx    = diff_list[ i ]->rhs;
      Enode * diff_p = diff_list[ j ]->lhs;
      Enode * idx_p  = diff_list[ j ]->rhs;

      if ( idx == idx_p )
	continue;

      Enode * a = diff->get1st( );
      Enode * b = diff->get2nd( );
      Enode * a_p = diff_p->get1st( );
      Enode * b_p = diff_p->get2nd( );
      vector< RewriteRule * > r_antec;
      vector< Enode * > e_antec;
      a = rewrite( g_rules, a, r_antec, e_antec );
      b = rewrite( g_rules, b, r_antec, e_antec );
      a_p = rewrite( g_rules, a_p, r_antec, e_antec );
      b_p = rewrite( g_rules, b_p, r_antec, e_antec );

      if ( a == a_p && b == b_p )
      {
	explain( r_antec );
      }
    }
  }

  if ( config.verbosity > 3 )
    cerr << "#  No failure" << endl;

  // Everything went fine
  status = l_True;
}

void RewriteEngine::addIndexEq( Enode * e )
{
  assert( e->isEq( ) );
  assert( e->getPolarity( ) == l_True );

  // Save state
  pushBacktrackPoint( );

  // Add rule to the set of index rules 
  vector< RewriteRule * > r_antec;
  addIndexRule( e->get1st( )
              , e->get2nd( )
	      , e
	      , r_antec );

  // Use rule to simplify current ground rules
  assert( ground_rules.empty( ) );

  // We don't know about the status
  status = l_Undef;
}

void RewriteEngine::remIndexEq( Enode * e )
{
  assert( e->isEq( ) );
  assert( e->getPolarity( ) == l_True );
  (void)e;

  // Restore state prior to eq
  popBacktrackPoint( );

  // We don't know about the status
  status = l_Undef;
}

void RewriteEngine::addIndexRule( Enode * l
                                 , Enode * r
				 , Enode * e
				 , vector< RewriteRule * > & r_antec )
{
  orient( &l, &r );
  vector< Enode * > e_antec;
  RewriteRule * rule = new RewriteRule( l, r, e, r_antec, e_antec );

  if ( l->isDiff( ) )
  {
    diff_list.push_back( rule );
    assert( diff_to_index.find( l ) 
         == diff_to_index.end( ) );
    diff_to_index[ l ] = r;
#ifdef PRODUCE_PROOF
    assert( config.produce_inter == 0 
	 || !isABcommon( l->get1st( ) ) 
	 || !isABcommon( l->get2nd( ) )
	 || isABcommon( r ) );
#endif
  }

  undo_stack_oper.push_back( ADD_INDEX_RULE );
  undo_stack_term.push_back( rule );

  if ( config.verbosity > 3 )
  {
    cerr << "#   (+) " << rule;
    // cerr << " " << rule->partitions;
    cerr << endl;
  }

  // We don't know about the status
  status = l_Undef;
}

void RewriteEngine::addEq ( Enode * e )
{
  assert( e->isEq( ) );
  assert( e->getPolarity( ) == l_True );

  // Save equality for later
  assert( e->get1st( )->getRetSort( ) == egraph.getSortElem( )
       || e->get1st( )->getRetSort( ) == egraph.getSortArray( ) );

  if ( e->get1st( )->getRetSort( ) == egraph.getSortElem( ) )
    select_equalities_to_add.push_back( e );
  else
    store_equalities_to_add.push_back( e );

  // We don't know about the status
  status = l_Undef;
}

void RewriteEngine::remEq( Enode * e )
{
  assert( e->isEq( ) );
  assert( e->getPolarity( ) == l_True );
  (void)e;

  if ( e->get1st( )->getRetSort( ) == egraph.getSortElem( ) )
    select_equalities_to_add.pop_back( );
  else
    store_equalities_to_add.pop_back( );

  // We don't know about the status
  status = l_Undef;
}

void RewriteEngine::addGroundRule( Enode * l, Enode * r, Enode * e )
{
  assert( e );

  vector< RewriteRule * > r_antec;
  vector< Enode * > e_antec;

#if REDUCE_TO_EUF
  config.incremental = true;

  e_antec.push_back( e );

  if ( l->getRetSort( ) == egraph.getSortElem( ) )
  {
    l = rewriteGeneric( l, e_antec );
    r = rewriteGeneric( r, e_antec );

#if SPLIT_ON_DEMAND
    const bool condl = l->isSelect( ) && l->get1st( )->isStore( );
    const bool condr = r->isSelect( ) && r->get1st( )->isStore( );
    const bool cond = candidate == NULL 
                   && (l != r) 
		   && ( condl || condr );
    assert( !condl || !condr );

    if ( cond )
    {
      Enode * sel = condl ? l : r;
      Enode * a = sel->get1st( );
      size_t idxs = 0;
      while ( a->isStore( ) ) 
      { 
	idxs ++; 
	a = a->get1st( ); 
      }
      if ( idxs > nof_idxs )
      {
	candidate = egraph.mkEq( egraph.cons( sel->get2nd( )
			       , egraph.cons( sel->get1st( )->get2nd( ) ) ) );
	nof_idxs = idxs;
      }
    }
#endif

    Enode * eq = egraph.mkEq( egraph.cons( l
	                    , egraph.cons( r ) ) );

    // Useless
    if ( eq == e )
      return;
    // Useless
    if ( eq->isTrue( ) ) 
      return;
    // Already there, do not add
    if ( eqs_to_antec.find( eq ) != eqs_to_antec.end( ) )
      return;

    assert( !eq->isFalse( ) );
    assert( eqs_to_antec.find( eq ) == eqs_to_antec.end( ) );

    /*
    cerr << "PRODUCED: " << eq << endl;
    cerr << "    FROM: " << e << endl;
    cerr << "   using: " << endl;
    for ( size_t i = 0 ; i < e_antec.size( ) ; i ++ )
    {
      cerr << "     " << e_antec[ i ] << endl;
    }
    */

    eqs_to_antec[ eq ] = e_antec;
  } 

#else // REDUCE_TO_EUF

  // Rewrite to simplify stores and selects generically
#if LESS_R1
  //
  // Avoids store simplification
  //
  if ( l->getRetSort( ) != egraph.getSortArray( ) )
  {
#endif
  l = rewriteGeneric( l, e_antec );
  r = rewriteGeneric( r, e_antec ); 
#if LESS_R1
  }
#endif

  assert( !l->isSelect( ) || l->get1st( )->isVar( ) );
  assert( !r->isSelect( ) || r->get1st( )->isVar( ) );

  bool is_A = true;
#ifdef PRODUCE_PROOF
  assert( l->getIPartitions( ) != 0 );
  assert( r->getIPartitions( ) != 0 );
  if ( config.produce_inter != 0 )
    is_A = isAlocal( l ) || isAlocal( r ) || isAlocal( e );
#else
  (void)is_A;
#endif

  addGroundRule( l                // lhs
               , r                // rhs
       	       , e                // Reason for rule
#ifdef PRODUCE_PROOF
       	       , is_A 
	         ? ground_rules   // Select A
		 : ground_rules_b // Select B
#else
	       , ground_rules
#endif
       	       , r_antec          // Empty antecedent reason 
       	       , e_antec          // Empty neq reason
       	       );

#endif // REDUCE_TO_EUF
}

void
RewriteEngine::addGroundRule( Enode * l
                             , Enode * r
			     , Enode * e 
			     , ground_rules_t & g_rules
			     , vector< RewriteRule * > & r_antec 
			     , vector< Enode * > & e_antec
			     )
{
#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0 || l->getIPartitions( ) != 0 );
  assert( config.produce_inter == 0 || r->getIPartitions( ) != 0 );
#endif

  // Save sizes to restore later
  const size_t r_antec_size = r_antec.size( );
  const size_t e_antec_size = e_antec.size( );

  assert( status == l_Undef );

  // Now indexes are different iff they are syntactically different
  l = rewriteGeneric( l, e_antec );
  r = rewriteGeneric( r, e_antec );

  if ( l == r ) 
  {
    r_antec.resize( r_antec_size );
    e_antec.resize( e_antec_size );
    return;
  }

  if ( r->isVar( ) && l->isStore( ) )
  {
    Enode * tmp = l;
    l = r;
    r = tmp;
  }
  
  const int badly_oriented = orient( &l, &r );

  // Check orientation w.r.t. ordering
  if ( badly_oriented != 0 )
  {
    assert( badly_oriented == 1 
	 || badly_oriented == 2 
	 || badly_oriented == 3 );

    if ( badly_oriented == 2 )
    {
#ifdef PRODUCE_PROOF
      // Postpone processing
      assert( config.produce_inter > 0 );
      // addBadlyOrientable( l, r, e, r_antec, e_antec );
      // MOD
      // return;
#endif
    }
    else if ( badly_oriented == 1 
	   || badly_oriented == 3 )
    {
      // Standard or interpolating badly orientable equality to be rotated
      Enode * a = l;
      Enode * b = r;
      assert( a->isVar( ) );
      assert( b->isStore( ) );
      vector< Enode * > indexes;
      vector< Enode * > elements;
      while( b->isStore( ) )
      {
	Enode * i = b->get2nd( );
	indexes.push_back( i );
	elements.push_back( b->get3rd( ) );
	b = b->get1st( );
      }

      // Reflexivity applies
      if ( a == b )
      {
	for ( size_t i = 0 ; i < indexes.size( ) ; i ++ )
	{
	  // Adds rd( a, I ) = E
	  Enode * sel = egraph.mkSelect( a, indexes[ i ] );
	  addAndComplete( sel, elements[ i ], NULL, g_rules, r_antec, e_antec );
	}
	return;
      }
      // Symmetry applies
      else
      {
	//
	// We have 
	// a = wr( b, I, D ) /\ rd( b, I ) = E
	//
	// We need to construct 
	// b = wr( a, I, E ) /\ rd( a, I ) = D
	//
	Enode * st = a;
	for ( size_t i = 0 ; i < indexes.size( ) ; i ++ )
	{
	  Enode * sel = egraph.mkSelect( b, indexes[ i ] );
	  Enode * old_st = st;
	  st = egraph.mkStore( old_st
	                     , indexes[ i ]
	                     , sel );

	  // Also add rd( a, i ) = e needed by symmetry
	  Enode * sym_sel = egraph.mkSelect( a, indexes[ i ] );

	  addAndComplete( sym_sel, elements[ i ], e
	                , g_rules
	                , r_antec
		        , e_antec );
	}

	vector< RewriteRule * > tmp1;
	vector< Enode * > tmp2;
	// Here we rewrite things like
	// rd( a, i ) 
	// into
	// d
	// because of asserted eqs in
	// preprocessing for indexes in store
	st = rewrite( g_rules, st, tmp1, tmp2 );
	l = b;
	r = st;

#ifdef PRODUCE_PROOF
	if ( badly_oriented == 3 )
	{
	  if ( isABcommon( l ) && !isABcommon( r ) )
	  {
	    // addBadlyOrientable( l, r, e, r_antec, e_antec );
	    // MOD
	    // return;
	  }
	}
#endif
      }
    }
  }

  // Add rule and trigger other completion 
  // steps C1,C2,C4,C5 (C3 is handled in check)
  addAndComplete( l, r, e, g_rules, r_antec, e_antec );
}

//
// This function takes care of critical pairs C1, C2, C4, C5
// C3 will be handled by function applyC3 once all other rules
// have been produced
//

void RewriteEngine::addAndComplete( Enode * l
                                  , Enode * r
				  , Enode * e
				  , ground_rules_t & g_rules
				  , vector< RewriteRule * > & r_antec_old
				  , vector< Enode * > & e_antec_old
				  , const bool propagated )
{
#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0 || l->getIPartitions( ) != 0 );
  assert( config.produce_inter == 0 || r->getIPartitions( ) != 0 );
#endif

#ifdef PRODUCE_PROOF
  if ( config.produce_inter != 0
    && l->isSelect( ) 
    && isABcommon( l )
    && !isABcommon( r ) )
  {
    addBadSelect( l, r, e, r_antec_old, e_antec_old );
    return;
  }
#endif

  Enode * key = l;

  if ( l->isSelect( ) )
    key = egraph.mkSelect( l->get1st( )
	                 , getRoot( l->get2nd( ) ) );

  map< Enode *, RewriteRule * >::iterator it = g_rules.find( key );
  bool safely_add = it == g_rules.end( );

  // Apply (R1) eagerly
  if ( safely_add )
  {
#if LESS_R1
    //
    // Avoids R1 on stores
    //
    if ( !r->isStore( ) )
#endif
    r = rewrite( g_rules, r, r_antec_old, e_antec_old );
  }

  // Create rule
  RewriteRule * new_rule = new RewriteRule( l, r, e, r_antec_old, e_antec_old, propagated );

#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0 || isAlocal( new_rule ) || isBlocal( new_rule ) );
  assert( config.produce_inter == 0 || !isAlocal( new_rule ) || &g_rules == &ground_rules );
  assert( config.produce_inter == 0 || !isBlocal( new_rule ) || &g_rules == &ground_rules_b );
#endif

  // printRules( g_rules );

  //
  // Case 1, lhs is not yet part of a rule, safely add
  //
  if ( safely_add )
  {
    g_rules[ key ] = new_rule;

#ifdef PRODUCE_PROOF
    if ( isAlocal( new_rule ) )
    {
#endif
      undo_stack_oper.push_back( ADD_GROUND_RULE );
      undo_stack_term.push_back( new_rule );
#ifdef PRODUCE_PROOF
    }
    else
    {
      undo_stack_oper.push_back( ADD_GROUND_B_RULE );
      undo_stack_term.push_back( new_rule );
    }
#endif


    if ( config.verbosity > 3 )
    {
      cerr << "#   (+) " << new_rule;
      cerr << endl;
    }

#ifdef PRODUCE_PROOF
    // Check if propagation is needed
    if ( config.produce_inter != 0 
      && isABcommon( l ) && isABcommon( r )
      && !propagated )
    {
      assert( isAlocal( new_rule ) || isBlocal( new_rule ) );
      vector< RewriteRule * > r_antec;
      vector< Enode * > e_antec; 
      r_antec.push_back( new_rule );
      assert( isAlocal( new_rule ) || isBlocal( new_rule ) );
      // Propagate rule to B
      if ( isAlocal( new_rule ) )
	addAndComplete( l, r, e, ground_rules_b, r_antec, e_antec, true );
      // Progagate rule to A
      else 
	addAndComplete( l, r, e, ground_rules, r_antec, e_antec, true );
    }
    // Check if badly orientable
    if ( r->isStore( ) )
    {
      Enode * inner_var = r;
      while ( !inner_var->isVar( ) )
	inner_var = inner_var->get1st( );

      if ( config.produce_inter != 0 )
      {
	// It is badly orientable
	if ( isABcommon( l ) 
	  && ( isAlocal( r ) || isBlocal( r ) ) )
	{
#if OUTSPLIT
	  if ( addNewIdx( l, inner_var ) )
	    return;
#endif
	  badly_orientable.push_back( new_rule ); 
	  undo_stack_oper.push_back( ADD_BADLY_ORIENTABLE );
	  undo_stack_term.push_back( new_rule );
	}
      }
    }
#endif

    return;
  }

  // Disable one parent rule (we just do not insert new_rule)
  undo_stack_oper.push_back( ADD_DISABLED_GROUND_RULE );
  undo_stack_term.push_back( new_rule );

  //
  // Case 2, lhs is already there --> critical pair found
  //
  RewriteRule * r_i = it->second;
  RewriteRule * r_j = new_rule;

  // Rules is already there, let's just get out of here
  if ( r_i->lhs == r_j->lhs
    && r_i->rhs == r_j->rhs )
  {
    return;
  }

  if ( config.verbosity > 4 )
  {
    cerr << "# CRITICAL PAIR FOUND " << endl;
    cerr << "#  " << r_i << endl;
    cerr << "#  " << r_j << " (not in database)" << endl;
  }

  vector< RewriteRule * > r_antec;
  r_antec.push_back( r_i );
  r_antec.push_back( r_j );

  vector< Enode * > e_antec;

  // For bad selects, need to add explanation
  if ( r_i->lhs != r_j->lhs )
  {
    assert( r_i->lhs->isSelect( ) );
    assert( r_j->lhs->isSelect( ) );
    assert( r_i->lhs->get2nd( ) != r_j->lhs->get2nd( ) );
    // egraph.explain( r_i->lhs->get2nd( ), r_j->lhs->get2nd( ), e_antec );
    indexExplain( r_i->lhs->get2nd( ), r_j->lhs->get2nd( ), e_antec );
  }

  Enode * rew_ri = rewrite( g_rules, r_i->rhs, r_antec, e_antec );
  Enode * rew_rj = rewrite( g_rules, r_j->rhs, r_antec, e_antec );

  // Case (C1) or (C2)
  if ( rew_ri->isStore( ) || rew_rj->isStore( ) )
  {
    if ( !storeEquiv( rew_ri, rew_rj ) )
    {
      // In C1 and C2 both parent rules are to be removed.
      // Disable already existing
      disableGroundRule( g_rules, r_i );
      // Apply cases C1 or C2. Calls addGroundRule inside
      applyC1C2( g_rules, r_i->lhs, rew_ri, rew_rj, r_antec, e_antec );
    }
  }
  // Case (C4) or (C5)
  else
  {
    addGroundRule( rew_ri
		 , rew_rj
		 , NULL
		 , g_rules
		 , r_antec
		 , e_antec );
  }
}

#if OUTSPLIT
bool RewriteEngine::addNewIdx( Enode * l, Enode * r )
{
  Enode * diff = egraph.mkDiff( l, r );
  if ( diff_to_index.find( diff ) != diff_to_index.end( ) )
    return false;

  // Otherwise create new diff
  Enode * idx = freshVarFrom( diff );
  Enode * diff_eq = egraph.
}
#endif

void RewriteEngine::applyC1C2( ground_rules_t & g_rules
                              , Enode * var
                              , Enode * rew_ri
                              , Enode * rew_rj 
			      , vector< RewriteRule * > & r_antec
			      , vector< Enode * > & e_antec
			      )
{
  Enode * a = rew_ri;
  Enode * b = rew_rj;
  vector< Enode * > a_indexes;
  vector< Enode * > b_indexes;
  map< Enode *, Enode * > a_idx_to_elem;
  map< Enode *, Enode * > b_idx_to_elem;
  set< Enode * > a_root_indexes;
  set< Enode * > ab_root_indexes;
  //
  // Remark 1: because of canonization of store terms,
  // there are no syntactic duplicates within stores.
  // However there may be semantic duplicates due to
  // indexes which we did not rewrite
  //
  // First step, we understand if its a C1 or a C2
  // At the same time we gather indexes in a and in b
  //
  while( a->isStore( ) ) 
  {
    a_indexes.push_back( a->get2nd( ) );
    a_idx_to_elem[ a->get2nd( ) ] = a->get3rd( );
    a_root_indexes.insert( getRoot( a->get2nd( ) ) );
    a = a->get1st( );
  }
  while( b->isStore( ) ) 
  {
    b_indexes.push_back( b->get2nd( ) );
    b_idx_to_elem[ b->get2nd( ) ] = b->get3rd( );

    if ( a_root_indexes.find( getRoot( b->get2nd( ) ) ) != a_root_indexes.end( ) )
      ab_root_indexes.insert( getRoot( b->get2nd( ) ) );

    b = b->get1st( );
  }
  assert( a->isVar( ) );
  assert( b->isVar( ) );
  //
  // OK Cool. Now we have 
  //
  // a_indexes       :   list of indexes appearing in rew_ri
  // b_indexes       :   "                            rew_rj
  // a_idx_to_elem   :   map from rew_ri indexes to elements
  // b_idx_to_elem   :   "        rew_rj "
  // ab_root_indexes :   roots of indexes in common, basically I
  //
  // Thery are equal: it's a Case (C2)
  //
  if ( a == b )
  {
    // 
    // We have to apply Confl lemma. So we need to
    // understand what is I, J, H, E, E', D, F
    //
    // Also we have to create
    // var --> wr( a, I, E )
    // That's what we do next
    //
    vector< Enode * > i_indexes;
    vector< Enode * > j_indexes;
    vector< Enode * > h_indexes;
    Enode * wr_term = a;
    for ( int i = a_indexes.size( ) - 1 ; i >= 0 ; i -- )
    {
      // Index not in I
      if ( ab_root_indexes.find( getRoot( a_indexes[ i ] ) ) ==
	   ab_root_indexes.end( ) )
      {
	j_indexes.push_back( a_indexes[ i ] );
	continue;
      }
      
      i_indexes.push_back( a_indexes[ i ] );
      wr_term = egraph.mkStore( wr_term, a_indexes[ i ], a_idx_to_elem[ a_indexes[ i ] ] );
    }
    //
    // We add var --> wr( a, I, E ) to the set of rules now
    //
    addGroundRule( var, wr_term, NULL, g_rules, r_antec, e_antec );
    //
    // Adds all E = E'
    //
    for ( size_t i = 0 ; i < i_indexes.size( ) ; i ++ )
    {
      bool found = false;
      for ( size_t j = 0 ; j < b_indexes.size( ) ; j ++ )
      {
	// Found match
	if ( getRoot( b_indexes[ j ] ) == getRoot( i_indexes[ i ] ) )
	{
	  const size_t e_antec_size = e_antec.size( );
	  // Explain if necessary
	  if ( b_indexes[ j ] != i_indexes[ i ] )
	  {
	    indexExplain( b_indexes[ j ], i_indexes[ i ], e_antec );
	    // egraph.explain( b_indexes[ j ], i_indexes[ i ], e_antec );
	  }

	  addGroundRule( b_idx_to_elem[ b_indexes[ j ] ]
	               , a_idx_to_elem[ i_indexes[ i ] ]
		       , NULL
		       , g_rules
		       , r_antec
		       , e_antec );

	  // Resize back if necessary
	  if ( b_indexes[ j ] != i_indexes[ i ] )
	    e_antec.resize( e_antec_size );

	  found = true;
	}
	else
	  h_indexes.push_back( b_indexes[ i ] );
      }
      assert( found );
    }
    //
    // Adds all rd(a,J) = D
    //
    for ( size_t i = 0 ; i < j_indexes.size( ) ; i ++ )
    {
      Enode * j = j_indexes[ i ];
      Enode * d = a_idx_to_elem[ j ];
      // This select on rew_rj for the purpose of
      // automatically detect index predicates to
      // use in e_antec of the generated rule
      Enode * sel = egraph.mkSelect( rew_rj, j );
      addGroundRule( sel, d, NULL, g_rules, r_antec, e_antec );
    }
    //
    // Adds all rd(b,H) = F
    //
    for ( size_t i = 0 ; i < h_indexes.size( ) ; i ++ )
    {
      Enode * h = h_indexes[ i ];
      Enode * f = b_idx_to_elem[ h ];
      // This select on rew_ri for the purpose of
      // automatically detect index predicates to
      // use in e_antec of the generated rule
      Enode * sel = egraph.mkSelect( rew_ri, h );       
      addGroundRule( sel, f, NULL, g_rules, r_antec, e_antec );
    }
  }
  // Case (C1)
  else 
  {
    // Notice that w.r.t. the paper we have
    //
    // a   is b_1
    // b   is b_2
    // var is a
    //
    // Swap structures if a < b
    if ( lessThan( a, b ) )
    {
      // Swap store terms
      Enode * tmp = rew_ri;
      rew_ri = rew_rj;
      rew_rj = tmp;
      // Swap a and b
      tmp = a;
      a = b;
      b = tmp;
      // Swap index collection
      a_indexes.swap( b_indexes );
      // Swap index maps
      a_idx_to_elem.swap( b_idx_to_elem );
    }

    // Now we have that a > b, and a is in rew_ri
    // Step 1: apply symm to var = rew_rj
    //         we start from the outermost index
    Enode * new_store = rew_rj;
    for ( size_t i = 0 ; i < a_indexes.size( ) ; i ++ )
    {
      // Save sizes
      const size_t r_antec_size = r_antec.size( );
      const size_t e_antec_size = e_antec.size( );
      // First adds rd( var, i ) = e
      Enode * read_var_i = egraph.mkSelect( var, a_indexes[ i ] );
      Enode * e = a_idx_to_elem[ a_indexes[ i ] ];
      addGroundRule( read_var_i, e, NULL, g_rules, r_antec, e_antec );
      // Second, construct store term
      Enode * read_a_i = egraph.mkSelect( a, a_indexes[ i ] );
      Enode * f = rewrite( g_rules, read_a_i, r_antec, e_antec );
      Enode * old_store = new_store;
      (void)old_store;
      new_store = egraph.mkStore( new_store, a_indexes[ i ], f );
      // Restore sizes
      r_antec.resize( r_antec_size ); 
      e_antec.resize( e_antec_size ); 
    }
    // Adds rule var --> var_store( rew_ri )
    addGroundRule( a, new_store, NULL, g_rules, r_antec, e_antec );
    // Adds rule var --> rew_rj
    addGroundRule( var, rew_rj, NULL, g_rules, r_antec, e_antec );
  }
}

void RewriteEngine::pushBacktrackPoint ( )
{
  // Save solver state if required
  assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
  backtrack_points.push_back( undo_stack_oper.size( ) );
}

void RewriteEngine::popBacktrackPoint ( )
{
  assert( backtrack_points.size( ) > 0 );
  size_t undo_stack_new_size = backtrack_points.back( );
  backtrack_points.pop_back( );
  backtrackToStackSize( undo_stack_new_size );
}

void RewriteEngine::backtrackToStackSize( size_t size )
{
  while ( undo_stack_oper.size( ) > size )
  {
    oper_t last_action = undo_stack_oper.back( );
    RewriteRule * rule = undo_stack_term.back( );

    undo_stack_oper.pop_back( );
    undo_stack_term.pop_back( );

    if ( last_action == ADD_GROUND_RULE )
    {
      if ( config.verbosity > 3 )
	cerr << "#   (-) " << rule << endl;

      remFromDatabase( ground_rules, rule );

      delete rule;
    }
#ifdef PRODUCE_PROOF
    else if ( last_action == ADD_DEFINE0 )
    {    
      assert( !def_stack.empty( ) ); 
      Enode * last = def_stack.back( );
      def_stack.pop_back( );
      assert( definitions.find( last ) != definitions.end( ) ); 
      definitions.erase( last );
      delete rule;
    }    
    else if ( last_action == INDEX_MERGE )
    {
      Enode * i = undo_stack_repl.back( ).first;
      Enode * j = undo_stack_repl.back( ).second;
      undo_stack_repl.pop_back( );
      egraph.tmpMergeEnd( i, j );
      assert( getRoot( i ) != getRoot( j ) );
    }
    else if ( last_action == REPLACED_RULE )
    {
      ground_rules_t & g_rules = config.produce_inter == 0 || isAlocal( rule ) 
	                       ? ground_rules 
			       : ground_rules_b ;

      Enode * key     = undo_stack_repl.back( ).first;
      Enode * new_key = undo_stack_repl.back( ).second;
      undo_stack_repl.pop_back( );

      assert( g_rules.find( new_key ) != g_rules.end( ) );
      // Removing this new key
      g_rules.erase( new_key );

      assert( g_rules.find( key ) == g_rules.end( ) );
      // Reinserting old key
      g_rules[ key ] = rule;

      if ( config.verbosity > 3 )
      {
	cerr << "#   (+) " << rule;
	cerr << endl;
      }
    }
    else if ( last_action == ADD_GROUND_B_RULE )
    {
      if ( config.verbosity > 3 )
	cerr << "#   (-) " << rule << endl;

      remFromDatabase( ground_rules_b, rule );

      delete rule;
    }
    else if ( last_action == ADD_REPL_GROUND_RULE )
    {
      if ( config.verbosity > 3 )
	cerr << "#   (R) " << rule << endl;

      remFromDatabase( ground_rules, rule );
    }
    else if ( last_action == ADD_REPL_GROUND_B_RULE )
    {
      if ( config.verbosity > 3 )
	cerr << "#   (R) " << rule << endl;

      remFromDatabase( ground_rules_b, rule );
    }
    else if ( last_action == SET_CUSTOM_LT )
    {
      Pair( Enode * ) p = undo_stack_cust.back( );
      undo_stack_cust.pop_back( );
      assert( custom_lt.find( p ) != custom_lt.end( ) );
      custom_lt.erase( p );
    }
    else if ( last_action == PROPAGATE_A_NEQ )
    {
      neq_list.pop_back( );
    }
    else if ( last_action == PROPAGATE_B_NEQ )
    {
      neq_list_b.pop_back( );
    }
    else if ( last_action == ADD_BAD_SELECT )
    {
      assert( !bad_selects.empty( ) );
      delete bad_selects.back( );
      bad_selects.pop_back( );
    }
    else if ( last_action == ADD_BADLY_ORIENTABLE )
    {
      assert( !badly_orientable.empty( ) );
      // delete badly_orientable.back( );
      badly_orientable.pop_back( );
    }
#endif
    else if ( last_action == ADD_DISABLED_GROUND_RULE )
    {
      delete rule;
    }
    /*
    else if ( last_action == ADD_GENERIC_RULE )
    {
      RewriteRule * r = generic_rules.back( );
      generic_rules.pop_back( );
      delete r;
    }
    */
    else if ( last_action == ADD_INDEX_RULE )
    {
      // RewriteRule * r = index_rules.back( );
      // index_rules.pop_back( );

      if ( rule->lhs->isDiff( ) )
      {
	assert( rule == diff_list.back( ) );
	diff_list.pop_back( );
	assert( diff_to_index.find( rule->lhs ) != diff_to_index.end( ) );
	diff_to_index.erase( rule->lhs );
	// assert( index_to_diff.find( r->rhs ) != index_to_diff.end( ) );
	// index_to_diff.erase( r->rhs );
      }

      if ( config.verbosity > 3 )
	cerr << "#   (-) " << rule << endl;

      delete rule;
    }
    else if ( last_action == DISABLE_RULE )
    {
#ifdef PRODUCE_PROOF
      ground_rules_t & g_rules = config.produce_inter == 0 || isAlocal( rule ) 
	                       ? ground_rules 
			       : ground_rules_b ;
#else
      ground_rules_t & g_rules = ground_rules;
#endif

      Enode * key = rule->lhs;

      if ( rule->lhs->isSelect( ) )
	key = egraph.mkSelect( rule->lhs->get1st( )
	                     , getRoot( rule->lhs->get2nd( ) ) );

      assert( g_rules.find( key ) == g_rules.end( ) );

      g_rules[ key ] = rule;

      if ( config.verbosity > 3 )
      {
	cerr << "#   (+) " << rule;
	cerr << endl;
      }
    }
  }

  assert( undo_stack_term.size( ) == undo_stack_oper.size( ) );
}

Enode * RewriteEngine::rewrite( ground_rules_t & g_rules
                               , Enode * e
                               , vector< RewriteRule * > & r_antec
			       , vector< Enode * > & e_antec )
{
  assert( e );

  bool saturated = false;
  Enode * result = e;
  while( !saturated )
  {
    Enode * res = rewriteGeneric( result, e_antec );
    res = rewriteGround( g_rules, res, r_antec, e_antec );
    saturated = result == res;
    result = res;
  }

  return result;
}

Enode * RewriteEngine::rewriteGeneric( Enode * e
                                     , vector< Enode * > & e_antec )
{
  assert( e );

#ifdef PRODUCE_PROOF
    assert( config.produce_inter == 0
	 || e->getIPartitions( ) != 0 );
#endif

  if ( e->isVar( ) )
    return e;

  assert( e->isSelect( ) || e->isStore( ) ); 

  Enode * new_e = NULL;

  if ( e->isSelect( ) )
  {
    // Scan the store term, until the index
    // is found, or the array variable is found
    Enode * a = e->get1st( );
    Enode * i = e->get2nd( );
    while( a->isStore( ) && new_e == NULL )
    {
      Enode * j = a->get2nd( );
      // The two indexes are equal modulo eq classes
      if ( getRoot( i ) == getRoot( j ) )
      {
	// Return overwriting element
	new_e = a->get3rd( );
	// If different indexes, need to explain why so
	if ( i != j )
	  // egraph.explain( i, j, e_antec );
	  indexExplain( i, j, e_antec );
      }
      else
      {
#if 1 || SPLIT_ON_DEMAND
	Enode * eq = egraph.mkEq( egraph.cons( i
		                , egraph.cons( j ) ) );
	// We can simplify further
	if ( eq->hasPolarity( ) )
	{
	  assert( eq->getPolarity( ) == l_False );
	  e_antec.push_back( eq );
	}
	// We stop simplification
	else
	  break;
#else
	e_antec.push_back( egraph.mkEq( egraph.cons( i
		                      , egraph.cons( j ) ) ) );
	assert( config.produce_inter != 0 
	     || e_antec.back( )->hasPolarity( ) );
	assert( config.produce_inter != 0
	     || e_antec.back( )->getPolarity( ) == l_False );
#endif
      }
      a = a->get1st( );
    }
    if ( new_e == NULL )
    {
#if 1 || SPLIT_ON_DEMAND
#else
      assert( a->isVar( ) );
#endif
      new_e = egraph.mkSelect( a, i );
    }
    // It might be a select, so simplify again
    else
    {
      new_e = rewriteGeneric( new_e, e_antec );
    }
#if 1 || SPLIT_ON_DEMAND
#else
    assert( new_e->isVar( ) 
	 || new_e->get1st( )->isVar( ) );
#endif
  }
  else
  {
    vector< Enode * > useful_stores;
    Enode * a = e;

    egraph.initDup1( );

    while ( a->isStore( ) ) 
    {
      // Old way
      // Enode * i = a->get2nd( );
      //
      // New way
      // Notice that we do
      // not need to store the reason
      // why a->get2nd( ) = a->get2nd( )->getRoot( )
      //
      // In fact such reasons are to be used only
      // when reading from a store, as stores on their
      // own cannot lead to a conflict !. So consider
      //
      // b --> wr( wr( a, i, e ), j, d )
      //
      // with i = j. Then we can simply use
      //
      // b --> wr( a, j, d )
      //
      // Later if we read on that, we have two cases
      //
      // rd( b, j ), in which i = j does not influece
      // rd( b, i ), in which i = j matters, but it's
      // already added when simplifying reads
      //
      Enode * i = getRoot( a->get2nd( ) );
      if ( !egraph.isDup1( i ) )
      {
	useful_stores.push_back( a );
	egraph.storeDup1( i );
      }
      a = a->get1st( );
    }

    egraph.doneDup1( );

    // Create the sorted term
    new_e = a;
    while ( !useful_stores.empty( ) ) 
    {
      Enode * old_new_e = new_e;
      Enode * elem = useful_stores.back( )->get3rd( );

#if 1
      vector< Enode * > tmp;
      Enode * rew_elem = rewriteGeneric( elem
				       , tmp );
#else
      Enode * rew_elem = rewriteGeneric( elem
				       , e_antec );
#endif

      new_e = egraph.mkStore( new_e
	                    , useful_stores.back( )->get2nd( )
			    , rew_elem
			    );

#ifdef PRODUCE_PROOF
      checkCanonizedStore( new_e );
#endif
      (void)old_new_e;
      useful_stores.pop_back( );
    }
  }

#ifdef PRODUCE_PROOF
    assert( config.produce_inter == 0
	 || new_e->getIPartitions( ) != 0 );
#endif

  return new_e;
}

Enode * RewriteEngine::rewriteGround( ground_rules_t & g_rules
                                     , Enode * e
                                     , vector< RewriteRule * > & r_antec
                                     , vector< Enode * > & e_antec )
{
  assert( e );

#ifdef PRODUCE_PROOF
    assert( config.produce_inter == 0
	 || e->getIPartitions( ) != 0 );
#endif

  map< Enode *, RewriteRule * > & cache = g_rules;

  egraph.initDupMap1( );
  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( e );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );

    Enode * result = NULL;
    map< Enode *, RewriteRule * >::iterator it;
    if ( enode->getArity( ) == 0 )
    {
      it = cache.find( enode );
      if ( it != cache.end( ) )
      {
	result = it->second->rhs;
	r_antec.push_back( it->second );
      }
      else
      {
	result = enode;
      }
    }
    else if ( enode->isDiff( ) )
    {
      result = enode;
    }
    else if ( enode->isSelect( ) )
    {
      Enode * a = egraph.valDupMap1( enode->get1st( ) );
      Enode * i = egraph.valDupMap1( enode->get2nd( ) );
      Enode * tmp = egraph.mkSelect( a, getRoot( i ) );

      it = cache.find( tmp );
      if ( it != cache.end( ) )
      {
	result = it->second->rhs;
	r_antec.push_back( it->second );
	assert( it->second->lhs->isSelect( ) );
	// Explain if indexes are different
	if ( it->second->lhs->get2nd( ) != i )
	  // egraph.explain( i, it->second->lhs->get2nd( ), e_antec );
	  indexExplain( i, it->second->lhs->get2nd( ), e_antec );
      }
      else
      {
	result = egraph.mkSelect( a, i );
      }
    }
    else if ( enode->isStore( ) )
    {
      Enode * a = egraph.valDupMap1( enode->get1st( ) );
      Enode * i = egraph.valDupMap1( enode->get2nd( ) );
      Enode * d = egraph.valDupMap1( enode->get3rd( ) );
      Enode * tmp = egraph.mkStore( a, i, d );
      it = cache.find( tmp );
      if ( it != cache.end( ) )
      {
	result = it->second->rhs;
	r_antec.push_back( it->second );
      }
      else
      {
	result = tmp;
      }
    }
    else
    {
      assert( false );
    }

    assert( result );

#ifdef PRODUCE_PROOF
    assert( config.produce_inter == 0
	 || result->getIPartitions( ) != 0 );
#endif

    egraph.storeDupMap1( enode, result );
  }

  Enode * new_e = egraph.valDupMap1( e );
  assert( new_e );

  egraph.doneDupMap1( );

#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0
       || new_e->getIPartitions( ) != 0 );
#endif

  return new_e;
}

void RewriteEngine::disableGroundRule( ground_rules_t & g_rules
                                      , RewriteRule * r )
{
  if ( config.verbosity > 3 )
    cerr << "#   (-) " << r << endl;

  // r->enabled = false;
  undo_stack_oper.push_back( DISABLE_RULE );
  undo_stack_term.push_back( r );

  remFromDatabase( g_rules, r );
}

void RewriteEngine::addNeq( Enode * e )
{
  assert( e->isEq( ) );
  // assert( e->getPolarity( ) == l_False );

  if ( e->getRetSort( ) == egraph.getSortArray( ) )
  {
    opensmt_error( "Negated array equalities not handled in the solver" );
  }
  
  neq_list.push_back( e );

  if ( config.verbosity > 3 )
    cerr << "#   (+) (not " << e << ")" << endl;

#ifdef PRODUCE_PROOF
  if ( config.produce_inter != 0
    && isABcommon( e->get1st( ) )
    && isABcommon( e->get2nd( ) ) )
  {
    neq_list_b.push_back( e );
    undo_stack_oper.push_back( PROPAGATE_B_NEQ );
    undo_stack_term.push_back( NULL );
    if ( config.verbosity > 3 )
      cerr << "#   (Propagating to B)" << endl;
  }
#endif

  // We don't know about the status
  status = l_Undef;
}

void RewriteEngine::remNeq( Enode * e )
{
  (void)e;
  assert( e->isEq( ) );
#ifdef PRODUCE_PROOF
  assert( config.produce_inter != 0 
       || e->getPolarity( ) == l_False );
#else
  assert( e->getPolarity( ) == l_False );
#endif

  Enode * tmp = neq_list.back( );
  (void)tmp;
  neq_list.pop_back( );

  assert( tmp == e );

  // We don't know about the status
  status = l_Undef;
}

void RewriteEngine::printNeqs( )
{
  cerr << "# Negated equalities" << endl;
  for ( size_t i = 0 ; i < neq_list.size( ) ; i ++ )
    cerr << "# " << i + 1 << ": " << neq_list[ i ] << endl;
}

void RewriteEngine::explain( vector< RewriteRule * > & r_antec )
{
#if PRINT_EXPL_DOT
  static int counter = 0;
  stringstream ss;
  ss << "expl_" << counter++ << ".dot";
  ofstream out( ss.str( ).c_str( ) );
  out << "digraph tmp {" << endl;
#endif

  set< RewriteRule * > seen;

  while ( !r_antec.empty( ) )
  {
    RewriteRule * r = r_antec.back( );
    r_antec.pop_back( );

    // Skip already seen
    if ( !seen.insert( r ).second )
      continue;
    
#if PRINT_EXPL_DOT
    string color = r->partitions == 2 ? "red"
                 : r->partitions == 4 ? "cyan"
		 : r->partitions == 6 ? "green"
		 : "white" ;

    stringstream ss;
    ss << "\"" << r->lhs->getId( ) << "_" 
       << r->rhs->getId( ) << "_" 
       << color << "\"" 
       << " [label=\"" << r << "\",style=filled,fillcolor=" << color << "]" << endl;
    out << ss.str( );
    if ( r->reason )
    {
      stringstream se;
      se << "\"" << r->reason->getId( )
	 << "_" << color << "\"" 
	 << " [label=\"" << r->reason << "\",shape=box,style=filled,fillcolor=" << color << "]" << endl;
      out << se.str( );
      stringstream ss;
      ss << "\"" << r->lhs->getId( ) << "_" 
	 << r->rhs->getId( ) << "_"
	 << color << "\"" << " -> "
	 << "\"" << r->reason->getId( )
	 << "_" << color << "\"";
      out << ss.str( ) << ";" << endl;
    }
#endif
    // Adds eqs
    for ( vector< RewriteRule * >::iterator it = r->r_antec.begin( )
	; it != r->r_antec.end( )
	; it ++ )
    {
#if PRINT_EXPL_DOT
      string color_a = (*it)->partitions == 2 ? "red"
	   	     : (*it)->partitions == 4 ? "cyan"
	   	     : (*it)->partitions == 6 ? "green"
		     : "white" ;
      stringstream ss;
      ss << "\"" << r->lhs->getId( ) << "_" 
	 << r->rhs->getId( ) << "_"
	 << color << "\"" << " -> "
	 << "\"" << (*it)->lhs->getId( ) << "_"
	 << (*it)->rhs->getId( ) << "_"
	 << color_a << "\"";
      out << ss.str( ) << ";" << endl;
#endif

      r_antec.push_back( *it );
    }
    // Adds neqs
    for ( vector< Enode * >::iterator it = r->e_antec.begin( )
	; it != r->e_antec.end( )
	; it ++ )
    {
      // If it does not have polarity it measn that it
      // was created within the theory solver, hence we
      // don't insert it in the conflict
      if ( !(*it)->hasPolarity( ) ) continue;

#if PRINT_EXPL_DOT
      stringstream se;
      se << "\"" << (*it)->getId( )
	 << "_" << color << "\"" 
	 << " [label=\"(not " << (*it) << ")\",shape=box,style=filled,fillcolor=" << color << "]" << endl;
      out << se.str( );
      stringstream ss;
      ss << "\"" << r->lhs->getId( ) << "_" 
	 << r->rhs->getId( ) << "_"
	 << color << "\"" << " -> "
	 << "\"" << (*it)->getId( )
	 << "_" << color << "\"";
      out << ss.str( ) << ";" << endl;
#endif

      // assert( (*it)->getPolarity( ) == l_False );
      if ( seen_in_expl.insert( *it ).second )
	explanation.push_back( *it );
    }
    if ( r->reason )
    {
      if ( seen_in_expl.insert( r->reason ).second )
	explanation.push_back( r->reason );
    }
  }

#if PRINT_EXPL_DOT
  out << "}" << endl;
  out.close( );
#endif

  if ( config.verbosity > 3 )
  {
    cerr << "#  Explanation: " << endl;
    for ( size_t i = 0 ; i < explanation.size( ) ; i ++ )
    {
      const bool sign = explanation[ i ]->getPolarity( ) == l_False;
      cerr << "#  " << (sign?"(not ":"     ") << explanation[ i ] << (sign?")":"") << endl;
    }
  }
}

void RewriteEngine::retrieveIndexes( Enode * e
                                   , vector< Enode * > & indexes )
{
  egraph.initDup1( );

  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( e );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !egraph.isDup1( arg ) )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );

    // Rule 1 or Rule 2
    if ( enode->getRetSort( ) == egraph.getSortIndex( ) )
      indexes.push_back( enode );

    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );
}

void RewriteEngine::remFromDatabase( ground_rules_t & g_rules
                                    , RewriteRule * rule )
{
  Enode * key = rule->lhs;

  if ( key->isSelect( ) )
    key = egraph.mkSelect( key->get1st( ), getRoot( key->get2nd( ) ) );

  // cerr << "key: " << key << endl;
  // printRules( g_rules );

  assert( g_rules.find( key ) != g_rules.end( ) );
  g_rules.erase( key );
}

Enode * RewriteEngine::getRoot( Enode * i )
{
  return i->getRoot( );
}

void RewriteEngine::indexExplain( Enode * i, Enode * j, vector< Enode * > & expl )
{
#ifdef PRODUCE_PROOF
  // We do not explain newly introduced indexes
  if ( config.produce_inter != 0 
    && ( new_indexes.find( i ) != new_indexes.end( )
      || new_indexes.find( j ) != new_indexes.end( ) ) )
    return;
#endif
  egraph.explain( i, j, expl );
}

bool RewriteEngine::storeEquiv( Enode * a, Enode * b )
{
  map< Enode *, Enode * > a_, b_;

  while ( a->isStore( ) )
  {
    a_[ getRoot( a->get2nd( ) ) ] = a->get3rd( );
    a = a->get1st( );
  }

  while ( b->isStore( ) )
  {
    b_[ getRoot( b->get2nd( ) ) ] = b->get3rd( );
    b = b->get1st( );
  }

  if ( a != b )
    return false;

  for ( map< Enode *, Enode * >::iterator it = a_.begin( )
      ; it != a_.end( )
      ; it ++ )
  {
    if ( b_[ it->first ] != it->second )
      return false;
  }

  return true;
}

//
// Functions for interpolation go here !
//
#ifdef PRODUCE_PROOF
//
// Replace old_i with new_i in rules
//
void RewriteEngine::replaceIndexInRules( ground_rules_t & g_rules
                                       , Enode * old_i
				       , Enode * new_i )
{
  assert( getRoot( old_i ) != getRoot( new_i ) );
  assert( config.produce_inter != 0 );

  vector< RewriteRule * > rules;

  for ( ground_rules_t::iterator it = g_rules.begin( )
      ; it != g_rules.end( )
      ; it ++ )
  {
    Enode * key = it->first;

    if ( key->isVar( ) )
      continue;

    assert( key->isSelect( ) );

    // We need to replace this
    if ( key->get2nd( ) == getRoot( old_i ) )
    {
      rules.push_back( it->second );
    }
  }

  // Remove all rules to be removed
  for ( size_t k = 0 ; k < rules.size( ) ; k ++ )
  {
    RewriteRule * rule = rules[ k ];
    disableGroundRule( g_rules, rule );
  }

  old_i = getRoot( old_i );
  new_i = getRoot( new_i );

  assert( getRoot( old_i ) != getRoot( new_i ) );
  egraph.tmpMergeBegin( old_i, new_i );
  assert( getRoot( old_i ) == getRoot( new_i ) );
  undo_stack_oper.push_back( INDEX_MERGE );
  undo_stack_term.push_back( NULL );
  undo_stack_repl.push_back( make_pair( old_i, new_i ) );

  // Reinsert rules 
  for ( size_t k = 0 ; k < rules.size( ) ; k ++ )
  {
    RewriteRule * rule = rules[ k ];
    addAndComplete( rule, g_rules );
  }
}

void RewriteEngine::informIdx( Enode * e )
{
  assert( config.produce_inter != 0 );
  idx_list.push_back( e );
}

void RewriteEngine::computeIdxEqClasses( )
{
  assert( config.produce_inter != 0 );
  for ( size_t i = 0 ; i < idx_list.size( ) ; i ++ )
  {
    Enode * idx = idx_list[ i ];
    if ( isAlocal( getIndexParts( idx ) ) )
      idx_eq_classes_a.insert( getRoot( idx ) );
    if ( isBlocal( getIndexParts( idx ) ) )
      idx_eq_classes_b.insert( getRoot( idx ) );
  }
}

bool RewriteEngine::areNewIdx( Enode * i, Enode * j )
{
  return new_indexes.find( i ) != new_indexes.end( )
      || new_indexes.find( j ) != new_indexes.end( );
}

void RewriteEngine::interpolate( Enode * neq
                               , vector< RewriteRule * > & r_antec )
{
  assert( config.produce_inter != 0 );
  Enode * interp = NULL;
  // assert( !explanation.empty( ) );

  // Unsat happened in A
  interp = turn_A ? egraph.mkFalse( ) : egraph.mkTrue( );

  ipartitions_t partitions = turn_A ? 2 : 4; 
  bool done = false;

  set< RewriteRule * > seen;
  vector< RewriteRule * > rev_frontier = r_antec;

  // Recursively explore the antecedents to construct interpolant
  list< Enode * > psi_list;
  // Push negated equality
  if ( neq ) 
    psi_list.push_back( neq );

  while( !done )
  {
    vector< RewriteRule * > new_frontier;
    while( !rev_frontier.empty( ) )
    {
      RewriteRule * rule = rev_frontier.back( );
      rev_frontier.pop_back( );

      // Don't process already seen rules
      if ( !seen.insert( rule ).second )
	continue;

      // Skip indexes
      if ( rule->lhs->getRetSort( ) == egraph.getSortIndex( ) )
	continue;

      // Node of the same partition, expand further
      if ( rule->partitions == partitions )
      {
	rev_frontier.insert( rev_frontier.end( )
	                   , rule->r_antec.begin( )
			   , rule->r_antec.end( ) );
      }
      // Otherwise Exchange happend. Store equality
      // We skip AB because they are indexes
      else 
      {
	new_frontier.push_back( rule );
	psi_list.push_back( egraph.mkEq( egraph.cons( rule->lhs
		                       , egraph.cons( rule->rhs ) ) ) );
      }
    }
    // Update interpolant and 
    // swap partitions, we have crossed the frontier !
    assert( partitions == 2 
  	 || partitions == 4 );
    Enode * psi = egraph.mkAnd( egraph.cons( psi_list ) );
    if ( partitions == 2 ) 
    {
      // Exchange 2
      interp = egraph.mkImplies( egraph.cons( psi, egraph.cons( interp ) ) );
      partitions = 4;
    }
    else if ( partitions == 4 ) 
    {
      // Exchange 1
      interp = egraph.mkAnd( egraph.cons( psi, egraph.cons( interp ) ) );
      partitions = 2;
    }

    assert( checkInterpolant( interp ) );

    // Reload frontier
    rev_frontier.swap( new_frontier );
    // Termination condition
    done = rev_frontier.empty( );

    psi_list.clear( );
  }

  assert( checkInterpolant( interp ) );

  interpolant = interp;
}

void RewriteEngine::iCheck( size_t level )
{
  assert( explanation.empty( ) );

  assert( config.produce_inter != 0 );
  assert( status == l_Undef );

  // cerr << "BEFORE CHECK" << endl;
  // cerr << "BEFORE CHECK" << endl;
  // cerr << "BEFORE CHECK" << endl;
  // printRules( ground_rules );
  // printRules( ground_rules_b );

  interpolant = NULL;

  // Check A part
  turn_A = true;
  check_( ground_rules, neq_list );

  if ( status == l_False )
  {
    assert( interpolant );
    accumulateAndFlushExplantion( );
    return;
  }

  status = l_Undef;

  // Check B part
  turn_A = false;
  check_( ground_rules_b, neq_list_b );

  if ( status == l_False )
  {
    assert( interpolant );
    accumulateAndFlushExplantion( );
    return;
  }

  //
  // Consider badly orientable eqs now
  //
  handleBadlyOrientable( level );
}

void RewriteEngine::handleBadlyOrientable( const size_t level )
{
  if ( level >= badly_orientable.size( ) )
    return;

  // Take bo to consider
  RewriteRule * bo = badly_orientable[ level ];

  // Skipping bo
  if ( bo_to_skip.find( bo ) != bo_to_skip.end( ) )
    return;

  if ( config.verbosity > 3 )
    cerr << "# " << level << ") Considering badly orientable: " << bo << endl;

  disableGroundRule( isAlocal( bo ) ? ground_rules : ground_rules_b, bo );

  // Find out what is I1, E1 and what is I2, E2
  vector< Enode * > i1, i2, e1, e2;

  Enode * c = bo->lhs;
  Enode * st = bo->rhs;
  while ( st->isStore( ) )
  {
    if ( isABcommon( getIndexParts( st->get2nd( ) ) )
      && isABcommon( st->get3rd( ) ) )
    {
      i1.push_back( st->get2nd( ) );
      e1.push_back( st->get3rd( ) );
    }
    else
    {
      i2.push_back( st->get2nd( ) );
      e2.push_back( st->get3rd( ) );
    }
    st = st->get1st( );
  }
  Enode * c_prime = st;

  // Now we construct wr( c_prime, I1, E1 )
  while ( !i1.empty( ) )
  {
    Enode * old_st = st;
    st = egraph.mkStore( old_st, i1.back( ), e1.back( ) );  
    i1.pop_back( );
    e1.pop_back( );
  }

  if ( config.verbosity > 3 )
    cerr << "# " << level << ") Guessing: " << bo->lhs << " --> " << st << endl;

  status = l_Undef;
  list< Enode * > disjuncts;

  vector< RewriteRule * > r_antec;
  vector< Enode * > e_antec;

  ground_rules_t & g_rules = isAlocal( bo ) ? ground_rules : ground_rules_b;
  //
  // Case 1: we guess c --> wr( c_prime, I1, E1 )
  //
  // Save current state
  pushBacktrackPoint( );

  r_antec.push_back( bo );

  // Adds simple case
  addGroundRule( c, st, NULL, g_rules, r_antec, e_antec );

  iCheck( level + 1 );

  // Restore state
  popBacktrackPoint( );

  // Everything was sat, cute !
  if ( status == l_True )
    return;

  assert( interpolant );
  disjuncts.push_back( interpolant );

  if ( config.verbosity > 3 )
    cerr << "#  Partial interpolant: " 
	 << interpolant 
	 << endl;

  // Save state
  pushBacktrackPoint( );

  status = l_Undef;
  //
  // Case 2: we need to try the expensive disjunctive cases (ouch!)
  //
  Enode * c_second = c_prime;
  Enode * saved_st = NULL;
  if ( c_prime != st )
  {
    // We need introducing a new c_second
    c_second = freshVarFrom( c );
    // Make sure the ordering is set correctly
    setCustomLessThan( c_second, c );
    setCustomLessThan( c_prime, c_second );
    // Also add c_second --> wr( c_prime, I1, E1 )
    addGroundRule( c_second, st, NULL, g_rules, r_antec, e_antec );
    saved_st = st;
  }
  // We need introducing diff( c, c_second ) = i
  Enode * diff = egraph.mkDiff( c, c_second );
  Enode * i = NULL;
  map< Enode *, Enode * >::iterator it = diff_to_index.find( diff );
  bool is_new = false;
  if ( it == diff_to_index.end( ) ) 
  {
    i = freshVarFrom( diff );
    new_indexes.insert( i );
    is_new = true;
  }
  else
  {
    i = it->second;
  }

  if ( config.verbosity > 3 )
    cerr << "# " << level << ") Index: " << i << " is for " << diff << endl;

  // We need introducing rd( c, i ) = d
  Enode * rd_c_i = egraph.mkSelect( c, i );
  Enode * d = freshVarFrom( rd_c_i );
  // We need introducing rd( c_second, i ) = d_second
  Enode * rd_c_second_i = egraph.mkSelect( c_second, i );
  Enode * d_second = freshVarFrom( rd_c_second_i );
  // Add negated equalities 
  Enode * neq = egraph.mkEq( egraph.cons( d
                           , egraph.cons( d_second ) ) );	
  // Pushes diff
  RewriteRule * rule = new RewriteRule( diff, i, NULL, r_antec, e_antec );
  diff_list.push_back( rule );
  internals.insert( rule );
  // We need introducing d != d_second
  if ( isAlocal( bo->rhs ) ) 
    addNeq( neq );
  else                       
    addNeqB( neq );
  // Add all of them
  // Now the actual disjunctive cases can start !

  bool is_sat = false;
  // Iterate through all the indexes 
  for ( size_t k = 0 ; k < i2.size( ) && !is_sat ; k ++ )
  {
    status = l_Undef;

    list< Enode * > idisjuncts;

    // Check that *it and i merge into something meaningful
    if ( unmergable( i2[ k ], i ) )
      continue;

    // Save state prior to outer guess
    pushBacktrackPoint( );

    if ( config.verbosity > 3 )
      cerr << "# " << level << ") Outer guess: " << i << " = " << i2[ k ] << endl;

    replaceIndexInRules( isAlocal( i2[ k ] ) 
	               ? ground_rules
	               : ground_rules_b
	               , i2[ k ]
	               , i );

    // Save state
    pushBacktrackPoint( );

    if ( config.verbosity > 3 )
      cerr << "# " << level << ")  Inner guess: all different for " << i << endl;
    
    assert( isAlocal( i2[ k ] ) || isBlocal( i2[ k ] ) );

    // Adds now c --> wr( c_second, I2 - i2[k] + i, E2 - e2[k] + d )
    st = c_second;
    for ( int j = i2.size( ) - 1 ; j >= 0 ; j -- )
    {
      Enode * old_st = st;
      if ( j == static_cast< int >( k ) )
	st = egraph.mkStore( old_st, i, d );
      else
	st = egraph.mkStore( old_st, i2[ j ], e2[ j ] );
    }

    addGroundRule( c, st, NULL, g_rules, r_antec, e_antec );

    // Rewrite bo and adds it 
    status = l_Undef;

    // Check !
    iCheck( level + 1 );

    if ( status == l_True )
      is_sat = true;
    else
    {
      if ( config.verbosity > 3 )
	cerr << "#  Partial interpolant: " 
	  << interpolant 
	  << endl;

      idisjuncts.push_back( interpolant ); 
    }

    // Backtrack
    popBacktrackPoint( );

    // Now we need to complete partitions. To do so,
    // we have to match i (which is ABcommon) with 
    // all the possible candidates from the opposite 
    // partition of i2[k]. We can avoid matching it
    // with partitions of same color of i2[k] since
    // we already said that it is in the same class
    // of i2[k], and those classes are already 
    // partitioned
    set< Enode * > & idx_eq_classes = isAlocal( bo ) 
                                    ? idx_eq_classes_b
				    : idx_eq_classes_a;

    for ( set< Enode * >::iterator it = idx_eq_classes.begin( )
	; it != idx_eq_classes.end( )
	; it ++ )
    {
      if ( config.verbosity > 3 )
	cerr << "# " << level << ")  Inner guess: " << i << " = " << *it << endl;

      // Check that *it and i merge into something meaningful
      if ( unmergable( *it, i ) )
	continue;

      // Save state
      pushBacktrackPoint( );

      assert( isAlocal( *it ) || isBlocal( *it ) );

      replaceIndexInRules( isAlocal( *it ) 
	                 ? ground_rules
		         : ground_rules_b
		         , *it
		         , i );

      // Rewrite bo and adds it 
      status = l_Undef;

      // Adds now rd( c, i ) --> d
      addGroundRule( rd_c_i, d, NULL, g_rules, r_antec, e_antec );
      // Adds now rd( c_second, i ) --> d_second
      addGroundRule( rd_c_second_i, d_second, NULL, g_rules, r_antec, e_antec );
      // Adds now c --> wr( c_second, I2 - i2[k] + i, E2 - e2[k] + d )
      addGroundRule( c, st, NULL, g_rules, r_antec, e_antec );

      // Check !
      iCheck( level + 1 );

      if ( status == l_True )
	is_sat = true;
      else
      {
	if ( config.verbosity > 3 )
	  cerr << "#  Partial interpolant: " 
	       << interpolant 
	       << endl;
	idisjuncts.push_back( interpolant ); 
      }

      if ( config.verbosity > 3 )
	cerr << "# " << level << ")  Inner guess: " << i << " = " << *it << " END" << endl;

      // Backtrack
      popBacktrackPoint( );
    }

    disjuncts.push_back( isAlocal( bo ) 
                       ? egraph.mkAnd( egraph.cons( idisjuncts ) )
		       : egraph.mkOr( egraph.cons( idisjuncts ) ) );

    // Restore before outer merge
    popBacktrackPoint( );

    if ( config.verbosity > 3 )
      cerr << "# " << level << ") Outer guess: " << i << " = " << i2[ k ] << " END" << endl;
  }

  // Now we undo everything
  if ( isAlocal( bo->rhs ) ) 
    remNeq( neq );
  else                       
    remNeqB( neq );

  if ( is_new )
    new_indexes.erase( i );
  diff_list.pop_back( );
  internals.erase( rule );
  delete rule;

  // Restore
  popBacktrackPoint( );

  if ( !is_sat )
  {
    status = l_False;    
    interpolant = isAlocal( bo ) 
                ? egraph.mkOr( egraph.cons( disjuncts ) )
		: egraph.mkAnd( egraph.cons( disjuncts ) );

    egraph.initDupMap1( );
    egraph.storeDupMap1( d_second, rd_c_second_i );
    interpolant = substitute( interpolant );
    egraph.doneDupMap1( );

    egraph.initDupMap1( );
    egraph.storeDupMap1( d, rd_c_i );
    interpolant = substitute( interpolant );
    egraph.doneDupMap1( );

    egraph.initDupMap1( );
    egraph.storeDupMap1( i, diff );
    interpolant = substitute( interpolant );
    egraph.doneDupMap1( );
    
    // Also, we need to remove newly introduced terms
    if ( saved_st != NULL )
    {
      egraph.initDupMap1( );
      egraph.storeDupMap1( c_second, saved_st );
      interpolant = substitute( interpolant );
      egraph.doneDupMap1( );
    }


    if ( config.verbosity > 3 )
      cerr << "# Final interpolant is: " << interpolant << endl;
  }

  assert( !is_sat || status == l_True ); 
  assert( status == l_True || status == l_False );
}

void RewriteEngine::addNeqB( Enode * e )
{
  assert( e->isEq( ) );
#ifdef PRODUCE_PROOF
  assert( config.produce_inter != 0
       || e->getPolarity( ) == l_False );
#else
  assert( e->getPolarity( ) == l_False );
#endif

  if ( e->getRetSort( ) == egraph.getSortArray( ) )
  {
    opensmt_error( "Negated array equalities not handled in the solver" );
  }

  neq_list_b.push_back( e );

  if ( config.verbosity > 3 )
    cerr << "#   (+) (not " << e << ")" << endl;

  if ( isABcommon( e->get1st( ) )
    && isABcommon( e->get2nd( ) ) )
  {
    neq_list.push_back( e );
    undo_stack_oper.push_back( PROPAGATE_A_NEQ );
    undo_stack_term.push_back( NULL );
    if ( config.verbosity > 3 )
      cerr << "#   (Propagating to A)" << endl;
  }

  // We don't know about the status
  status = l_Undef;
}

void RewriteEngine::remNeqB( Enode * e )
{
  (void)e;
  assert( e->isEq( ) );
#ifdef PRODUCE_PROOF
  assert( config.produce_inter != 0
       || e->getPolarity( ) == l_False );
#else
  assert( e->getPolarity( ) == l_False );
#endif

  Enode * tmp = neq_list_b.back( );
  (void)tmp;
  neq_list_b.pop_back( );

  assert( tmp == e );

  // We don't know about the status
  status = l_Undef;
}

void RewriteEngine::addBadSelect( Enode * l
                                , Enode * r
				, Enode * e
				, vector< RewriteRule * > & r_antec
				, vector< Enode * > & e_antec )
{
  RewriteRule * rule = new RewriteRule( l, r, e, r_antec, e_antec );
  bad_selects.push_back( rule );

  if ( config.verbosity > 3 )
    cerr << "#   (b) " << rule << endl;

  undo_stack_oper.push_back( ADD_BAD_SELECT );
  undo_stack_term.push_back( rule );
}

void RewriteEngine::addBadlyOrientable( Enode * l
                                      , Enode * r
				      , Enode * e
				      , vector< RewriteRule * > & r_antec
				      , vector< Enode * > & e_antec )
{
  assert( false );
  RewriteRule * rule = new RewriteRule( l, r, e, r_antec, e_antec );
  badly_orientable.push_back( rule );

  if ( config.verbosity > 3 )
    cerr << "#   (b) " << rule << endl;

  undo_stack_oper.push_back( ADD_BADLY_ORIENTABLE );
  undo_stack_term.push_back( rule );
}

// Return the enode in the equivalence class of
// e with the highest partition. By highest we mean
// AB > A, B
Enode *
RewriteEngine::getIndexParts( Enode * e )
{
  if ( isABcommon( e ) )
    return e;

  assert( isAlocal( e ) || isBlocal( e ) );

  const Enode * vstart = e;
  for (;;)
  {
    e = e->getNext( );
    if ( isABcommon( e ) ) return e;
    if ( e == vstart ) return e;
  }
}

bool
RewriteEngine::checkInterpolant( Enode * f )
{
  // Check that variables are ABcommon
  assert( f );

  egraph.initDup1( );

  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( f );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );

    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !egraph.isDup1( arg ) )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );

    if ( enode->isVar( ) && !isABcommon( enode ) )
    {
      egraph.doneDup1( );
      return false;
    }

    assert( !egraph.isDup1( enode ) );
    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );

  return true;
}

bool
RewriteEngine::checkInvariants( Enode * l, Enode * r )
{
  if ( config.produce_inter == 0 )
    return true;

  if ( r->isStore( ) )
  {
    while( r->isStore( ) ) r = r->get1st( );
    if ( !greaterThan( l, r ) )
      return false;
  }

  // Invariant (i) and (ii)
  if ( isABcommon( l ) && !isABcommon( r ) )
    return false;

  // Invariant (iii)
  if ( r->isStore( ) && isABcommon( r ) && !isABcommon( l ) )
    return false;

  return true;
}

bool RewriteEngine::isABcommon( Enode * e )
{
  assert( config.produce_inter > 0 );
  ipartitions_t mask = 3;
  mask = ~mask;
  // Compute some useful conditions
  const ipartitions_t & parts = e->getIPartitions( );
  const bool is_AB = (parts & ~mask) != 0 
                  && (parts &  mask) != 0;
  return is_AB;
}

bool RewriteEngine::isAlocal( Enode * e )
{
  assert( config.produce_inter > 0 );
  ipartitions_t mask = 3;
  mask = ~mask;
  // Compute some useful conditions
  const ipartitions_t & parts = e->getIPartitions( );
  const bool is_A = !isABcommon( e ) 
                 && (parts & ~mask) != 0 ;
  return is_A;
}

bool RewriteEngine::isBlocal( Enode * e )
{
  assert( config.produce_inter > 0 );
  const bool is_B = !isABcommon( e ) 
                 && !isAlocal( e );
  return is_B;
}

bool RewriteEngine::isABcommon( RewriteRule * e )
{
  assert( config.produce_inter > 0 );
  ipartitions_t mask = 3;
  mask = ~mask;
  // Compute some useful conditions
  const ipartitions_t & parts = e->partitions;
  const bool is_AB = (parts & ~mask) != 0 
                  && (parts &  mask) != 0;
  return is_AB;
}

bool RewriteEngine::isAlocal( RewriteRule * e )
{
  assert( config.produce_inter > 0 );
  ipartitions_t mask = 3;
  mask = ~mask;
  // Compute some useful conditions
  const ipartitions_t & parts = e->partitions;
  const bool is_A = !isABcommon( e ) 
                 && (parts & ~mask) != 0 ;
  return is_A;
}

bool RewriteEngine::isBlocal( RewriteRule * e )
{
  assert( config.produce_inter > 0 );
  const bool is_B = !isABcommon( e ) 
                 && !isAlocal( e );
  return is_B;
}

void
RewriteEngine::setCustomLessThan( Enode * e1, Enode * e2 )
{
  assert( config.produce_inter != 0 );
  Pair( Enode * ) entry = make_pair( e1, e2 );
  // Reverse should not be there ...
  assert( custom_lt.find( make_pair( e2, e1 ) ) == custom_lt.end( ) );
  if ( custom_lt.insert( entry ).second )
  {
    undo_stack_oper.push_back( SET_CUSTOM_LT );
    undo_stack_term.push_back( NULL );
    undo_stack_cust.push_back( entry );
  }
  assert( lessThan( e1, e2 ) );
}

Enode *
RewriteEngine::freshVarFrom( Enode * e )
{
  char buf[ 32 ];
  stringstream ss;
  if ( e->getRetSort( ) == egraph.getSortArray( ) )
    ss << "Array";
  else
    ss << e->getRetSort( );
  sprintf( buf, "__%s_%lu"
              , ss.str( ).c_str( )
	      , egraph.nofEnodes( ) + 1 );
  egraph.newSymbol( buf, NULL, e->getRetSort( ) );
  Enode * var = egraph.mkVar( buf );
  return var;
}

void RewriteEngine::accumulateAndFlushExplantion( )
{
  // Otherwise it was unsat
  // accumulate conflict
  if ( explanation.empty( ) )
    return;

  acc_expl.insert( acc_expl.end( )
                 , explanation.begin( )
		 , explanation.end( ) );
  explanation.clear( );
}

Enode * RewriteEngine::getInterpolant( )
{
  return interpolant;
}

Enode * 
RewriteEngine::substitute( Enode * f )
{
  assert( f );

  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( f );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );

    //
    // Skip if the node has already been processed before
    //
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );

    Enode * result = egraph.copyEnodeEtypeTermWithCache( enode );

    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * result = egraph.valDupMap1( f );
  assert( result );

  return result;
}

bool RewriteEngine::unmergable( Enode * i, Enode * j )
{
  assert( i );
  assert( j );

  if ( !i->hasCongData( ) ) return false;
  if ( !j->hasCongData( ) ) return false;

  /*
  cerr << "Checking if " << i << " and " << j << " are mergable" << endl;

  cerr << "i class: " << endl;
  Enode * vs = i;
  Enode * es = i;
  for ( ; es != vs ; )
  {
    cerr << "  " << es << endl;
    es = es->getNext( );
  }

  cerr << "j class: " << endl;
  vs = j;
  es = j;
  for ( ; es != vs ; )
  {
    cerr << "  " << es << endl;
    es = es->getNext( );
  }
  */

  bool found_A = false, found_B = false;

  // Exhamine i class
  Enode * vstart = i;
  Enode * e = i;
  do
  {
    if ( isAlocal( e ) ) found_A = true;
    if ( isBlocal( e ) ) found_B = true;
    e = e->getNext( );
  }
  while( e != vstart );

  if ( !found_A && !found_B )
    return false;

  // if ( found_A ) cerr << "  i contains A" << endl;
  // if ( found_B ) cerr << "  i contains B" << endl;

  // Exhamine j class
  vstart = j;
  e = j;
  do
  {
    if ( isAlocal( e ) && found_A ) 
    { 
      // cerr << "UNMERGABLE !" << endl;
      return true;
    }
    if ( isBlocal( e ) && found_B ) 
    {
      // cerr << "UNMERGABLE !" << endl;
      return true;
    }
    e = e->getNext( );
  }
  while( e != vstart );

  return false;
}

void RewriteEngine::addAndComplete( RewriteRule * rule
				  , ground_rules_t & g_rules )
{
  assert( config.produce_inter != 0 );

  assert( rule->lhs->isSelect( ) );

  Enode * key = egraph.mkSelect( rule->lhs->get1st( )
	                       , getRoot( rule->lhs->get2nd( ) ) );

  map< Enode *, RewriteRule * >::iterator it = g_rules.find( key );
  bool safely_add = it == g_rules.end( );

  //
  // Case 1, lhs is not yet part of a rule, safely add
  //
  if ( safely_add )
  {
    g_rules[ key ] = rule;

    if ( isAlocal( rule ) )
    {
      undo_stack_oper.push_back( ADD_REPL_GROUND_RULE );
      undo_stack_term.push_back( rule );
    }
    else
    {
      undo_stack_oper.push_back( ADD_REPL_GROUND_B_RULE );
      undo_stack_term.push_back( rule );
    }

    if ( config.verbosity > 3 )
    {
      cerr << "#   (r) " << rule;
      cerr << endl;
    }

    // No propagation is necessary !
    // How come ? Boh !
    assert( !isABcommon( rule->lhs )
	 || !isABcommon( rule->rhs ) );

    return;
  }

  // Don't touch this rule, it has to survive during 
  // backtracking ...
  // FIXME: ????
  // undo_stack_oper.push_back( ADD_DISABLED_GROUND_RULE );
  // undo_stack_term.push_back( rule );

  //
  // Case 2, lhs is already there --> critical pair found
  //
  RewriteRule * r_i = it->second;
  RewriteRule * r_j = rule;

  // Rules is already there, let's just get out of here
  if ( r_i->lhs == r_j->lhs
    && r_i->rhs == r_j->rhs )
  {
    return;
  }

  if ( config.verbosity > 3 )
  {
    cerr << "# CRITICAL PAIR FOUND " << endl;
    cerr << "#  " << r_i << endl;
    cerr << "#  " << r_j << " (not in database)" << endl;
  }

  vector< RewriteRule * > r_antec;
  r_antec.push_back( r_i );
  r_antec.push_back( r_j );

  vector< Enode * > e_antec;

  // For bad selects, need to add explanation
  if ( r_i->lhs != r_j->lhs )
  {
    assert( r_i->lhs->isSelect( ) );
    assert( r_j->lhs->isSelect( ) );
    assert( r_i->lhs->get2nd( ) != r_j->lhs->get2nd( ) );
    assert( getRoot( r_i->lhs->get2nd( ) ) != 
	    getRoot( r_j->lhs->get2nd( ) ) );
    indexExplain( r_i->lhs->get2nd( ), r_j->lhs->get2nd( ), e_antec );
  }

  Enode * rew_ri = rewrite( g_rules, r_i->rhs, r_antec, e_antec );
  Enode * rew_rj = rewrite( g_rules, r_j->rhs, r_antec, e_antec );

  // Case (C1) or (C2)
  if ( rew_ri->isStore( ) || rew_rj->isStore( ) )
  {
    // In C1 and C2 both parent rules are to be removed.
    // Disable already existing
    disableGroundRule( g_rules, r_i );
    // Apply cases C1 or C2. Calls addGroundRule inside
    applyC1C2( g_rules, r_i->lhs, rew_ri, rew_rj, r_antec, e_antec );
  }
  // Case (C4) or (C5)
  else
  {
    addGroundRule( rew_ri
		 , rew_rj
		 , NULL
		 , g_rules
		 , r_antec
		 , e_antec );
  }
}

void RewriteEngine::replaceInRules( Enode *, Enode * )
{
  assert( false );
  /*
  assert( isAlocal( r ) || isBlocal( r ) );
  assert( isABcommon( r_prime ) );

  ground_rules_t & g_rules = isAlocal( r ) 
                           ? ground_rules
			   : ground_rules_b ;

  vector< RewriteRule * > to_remove;
  vector< Pair( Enode * ) > to_add;
  for ( ground_rules_t::iterator it = g_rules.begin( )
      ; it != g_rules.end( )
      ; it ++ )
  {
    RewriteRule * rule = it->second;

    egraph.initDupMap1( );
    egraph.storeDupMap1( r, r_prime );
    Enode * new_rhs = substitute( rule->rhs );
    assignPartitionsFrom( new_rhs, rule->rhs );
    egraph.doneDupMap1( );

    egraph.initDupMap1( );
    egraph.storeDupMap1( r, r_prime );
    Enode * new_lhs = substitute( rule->lhs );
    assignPartitionsFrom( new_lhs, rule->lhs );
    egraph.doneDupMap1( );

    if ( new_lhs != rule->lhs 
      || new_rhs != rule->rhs )
    {
      to_remove.push_back( rule );
      to_add.push_back( make_pair( new_lhs, new_rhs ) );
    }
  }
  for ( size_t i = 0 ; i < to_remove.size( ) ; i ++ )
  {
    RewriteRule * rule = to_remove[ i ];
    Enode * new_lhs = to_add[ i ].first;
    Enode * new_rhs = to_add[ i ].second;
    // Disable old
    disableGroundRule( g_rules, rule );
    vector< RewriteRule * > r_antec;
    r_antec.push_back( rule );
    vector< Enode * > e_antec;
    // Adds new
    addAndComplete( new_lhs, new_rhs, NULL, g_rules, r_antec, e_antec );
  }
  */
}

//
// Adds a new negated equalities, in which we replace
// r with r_prime. Also, we propagate the inequality
// if it gets ab-common
//
void RewriteEngine::replaceInNeqs( Enode * r, Enode * r_prime )
{
  assert( isAlocal( r ) || isBlocal( r ) );
  vector< Enode * > & this_neq_list = isAlocal( r ) 
                                    ? neq_list
			  	    : neq_list_b ;

  vector< Enode * > & other_neq_list = isAlocal( r ) 
                                     ? neq_list_b
			  	     : neq_list ;

  vector< Enode * > to_add;

  for ( size_t i = 0 ; i < this_neq_list.size( ) ; i ++ )
  {
    Enode * neq = this_neq_list[ i ];
    Enode * new_neq = NULL;

    if ( neq->get1st( ) == r ) 
    {
      new_neq = egraph.mkEq( egraph.cons( r_prime
                           , egraph.cons( neq->get2nd( ) ) ) );
    }
    if ( neq->get2nd( ) == r ) 
    {
      new_neq = egraph.mkEq( egraph.cons( neq->get1st( )
                           , egraph.cons( r_prime ) ) );
    }
    if ( new_neq )
    {
      to_add.push_back( new_neq );
    }
  }

  for ( size_t i = 0 ; i < to_add.size( ) ; i ++ )
  {
    if ( config.verbosity > 4 )
      cerr << "# Adding negated equality: " << to_add[ i ] << endl;

    this_neq_list.push_back( to_add[ i ] ); 

    undo_stack_oper.push_back( isAlocal( r ) 
	                     ? PROPAGATE_A_NEQ
			     : PROPAGATE_B_NEQ );
    undo_stack_term.push_back( NULL );

    if ( isABcommon( to_add[ i ]->get1st( ) ) 
      && isABcommon( to_add[ i ]->get2nd( ) ) )
    {
      if ( config.verbosity > 4 )
	cerr << "# Propagating negated equality: " << to_add[ i ] << endl;

      other_neq_list.push_back( to_add[ i ] ); 

      undo_stack_oper.push_back( isAlocal( r ) 
	                       ? PROPAGATE_B_NEQ
	                       : PROPAGATE_A_NEQ );
      undo_stack_term.push_back( NULL );
    }
  }
}

void RewriteEngine::fixBadSelect( )
{
  for ( size_t i = 0 ; i < bad_selects.size( ) ; i ++ )
  {
    RewriteRule * rule = bad_selects[ i ];
    // Adds a new definition
    assert( config.produce_inter != 0 );
    Enode * l = rule->lhs;
    Enode * r = rule->rhs;
    Enode * r_prime = freshVarFrom( l );
    assert( definitions.find( r_prime ) == definitions.end( ) );
    definitions[ r_prime ] = l;
    def_stack.push_back( r_prime );

    undo_stack_oper.push_back( ADD_DEFINE0 );
    undo_stack_term.push_back( NULL );

    // Apply reduction on rhs -- simulates replacement
    // replaceInRules( r, r_prime );
    vector< RewriteRule * > r_antec;
    r_antec.push_back( rule );
    vector< Enode * > e_antec;

    // Adds l --> r_prime
    addAndComplete( l, r_prime, NULL, isAlocal( r )
	                            ? ground_rules
				    : ground_rules_b
				    , r_antec
				    , e_antec );
    // Adds r --> r_prime
    addAndComplete( r, r_prime, NULL, isAlocal( r )
	                            ? ground_rules
				    : ground_rules_b
				    , r_antec
				    , e_antec );

    replaceInNeqs( r, r_prime );
  }
}

void RewriteEngine::fixBadlyOrientable( )
{
  for ( size_t k = 0 ; k < badly_orientable.size( ) ; k ++ )
  {
    RewriteRule * bo = badly_orientable[ k ];

    if ( !bo->enabled )
    {
      bo_to_skip.insert( bo );
      continue;
    }

    Enode * l = bo->lhs;
    Enode * r = bo->rhs;

    vector< Enode * > indexes;
    Enode * a = l;
    Enode * b = r;
    while ( b->isStore( ) ) 
    {
      indexes.push_back( b->get2nd( ) );
      b = b->get1st( );
    }
  
    Enode * diff = egraph.mkDiff( a, b );
    map< Enode *, Enode * >::iterator it = diff_to_index.find( diff );
    // There is a diff already coming from outside ...
    // this means that the value of the index is
    // already guessed
    if ( it != diff_to_index.end( ) )
    {
      bo_to_skip.insert( bo );
      disableGroundRule( isAlocal( bo ) ? ground_rules : ground_rules_b, bo );

      bool found = false;
      for ( size_t i = 0 ; i < indexes.size( ) && !found ; i ++ )
	found = getRoot( it->second ) == getRoot( indexes[ i ] );

      if ( !found )
      {
	vector< RewriteRule * > r_antec;
	vector< Enode * > e_antec;
	r_antec.push_back( bo );
	addAndComplete( a, b, NULL
	              , isAlocal( bo ) 
		        ? ground_rules
			: ground_rules_b
		      , r_antec, e_antec );
      }
      // Otherwise there are already 
      // rd( a, i ) != rd( b, i )
    }

    // Preprocess to see if it is a fake badly orientable
    if ( r->isStore( )
      && isABcommon( l )
      && !isABcommon( r ) )
    {
      // First: try to rewrite, it may become ABcommon ...
      // FIXME: check that tmp1, tmp2 have to be used
      vector< RewriteRule * > tmp1;
      vector< Enode * > tmp2;
      Enode * new_rhs = rewriteGround( isAlocal( r ) 
	                             ? ground_rules 
				     : ground_rules_b
				     , r
	                             , tmp1
	                             , tmp2 );
      if ( isABcommon( new_rhs ) )
      {
	bo_to_skip.insert( bo );
	disableGroundRule( isAlocal( bo ) ? ground_rules : ground_rules_b, bo );

	vector< RewriteRule * > r_antec;
	vector< Enode * > e_antec;
	r_antec.push_back( bo );
	addGroundRule( l, new_rhs, NULL, isAlocal( bo ) 
	             ? ground_rules
	             : ground_rules_b
	             , r_antec, e_antec );
      }
      else
      {
	// Process rules of the kind a --> wr( b, i, e )
	// where i is ABcommon but e is not
	Enode * b = r;
	vector< Enode * > indexes;
	vector< Enode * > elements;
	bool found_one = false;
	while( b->isStore( ) )
	{
	  indexes.push_back( b->get2nd( ) );
	  if ( isABcommon( b->get2nd( ) )
	    && !isABcommon( b->get3rd( ) ) )
	  {
	    Enode * rd = egraph.mkSelect( l, indexes.back( ) );
	    assert( isABcommon( l ) );
	    vector< RewriteRule * > tmp1;
	    vector< Enode * > tmp2;
	    // Since it is an ABcommon rule, it shall
	    // be present in both ground_rules and ground_rules_b
	    Enode * d = rewrite( ground_rules, rd, tmp1, tmp2 );	
	    elements.push_back( d );
	    // Adds correspondence
	    vector< RewriteRule * > r_antec;
	    vector< Enode * > e_antec;
	    r_antec.push_back( bo );
	    addAndComplete( b->get3rd( )
		          , d
			  , NULL
			  , isAlocal( b->get3rd( ) ) 
		          ? ground_rules 
			  : ground_rules_b
	                  , r_antec
	                  , e_antec );
	    found_one = true;
	  }
	  else
	    elements.push_back( b->get3rd( ) );

	  b = b->get1st( );
	}
	// Rewrite if found one
	if ( found_one )
	{
	  while( !indexes.empty( ) )
	  {
	    Enode * i = indexes.back( );
	    Enode * e = elements.back( );
	    indexes.pop_back( );
	    elements.pop_back( );
	    b = egraph.mkStore( b, i, e );
	  }

	  bo_to_skip.insert( bo );
	  disableGroundRule( isAlocal( bo ) ? ground_rules : ground_rules_b, bo );

	  vector< RewriteRule * > r_antec;
	  vector< Enode * > e_antec;
	  r_antec.push_back( bo );
	  addGroundRule( l, b, NULL, isAlocal( bo ) 
	               ? ground_rules
	               : ground_rules_b
	               , r_antec, e_antec );
	}
      }
    }
  }
}

bool RewriteEngine::checkCanonizedStore( Enode * e )
{
  while( e->isStore( ) )
  {
    if ( !e->get3rd( )->isVar( ) )
      return false;
    e = e->get1st( );
  }
  return true;
}
#endif
//
// Debugging functions go here
//
void RewriteEngine::printRules( ground_rules_t & g_rules )
{
  cerr << "List of rules " << (&g_rules == &ground_rules ? "A" : "B") << " : " << endl;
  for ( ground_rules_t::iterator it = g_rules.begin( )
      ; it != g_rules.end( )
      ; it ++ )
  {
    cerr << "  " << it->first << " : " << it->second << endl;
  }
}

void RewriteEngine::deduce( )
{

}
