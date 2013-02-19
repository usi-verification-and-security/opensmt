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

#include "Egraph.h"
#include "Enode.h"
//#include "LA.h"
// DO NOT REMOVE THIS COMMENT !!
// IT IS USED BY CREATE_THEORY.SH SCRIPT !!
// NEW_THEORY_HEADER
//#include "EmptySolver.h"
//#include "BVSolver.h"
//#include "LRASolver.h"
//#include "DLSolver.h"
//#include "CostSolver.h"
//#include "AXDiffSolver.h"
// Added to support compiling templates
//#include "DLSolver.C"
#include "SimpSMTSolver.h"

#define VERBOSE 0

//
// Inform the solver about the existence of node e
//

//lbool Egraph::inform( ERef e )
//{
//  assert( e != ERef_Undef );
//  assert( theoryInitialized );
//
//#ifdef PRODUCE_PROOF
//  assert( config.produce_inter == 0 
//       || e->getIPartitions( ) != 0 );
//#endif
//
//  lbool status;
//  Enode& en_e = enode_store[e];
//  map< enodeid_t, lbool >::iterator it = informed.find( en_e.getId( ) );
//
//  if ( it == informed.end( ) )
//  {
//    if ( en_e.getId( ) >= (enodeid_t)id_to_belong_mask.size_( ) )
//      id_to_belong_mask.growTo( en_e.getId( ) + 1, 0 );
//
//    // If congruence is running enode is initialized by
//    // the appropriate routine initializeCongInc on demand
//    // only if necessary
//    if ( !congruence_running )
//      initializeCong( e );
//
//    assert( id_to_belong_mask[ en_e.getId( ) ] == 0 );
//
//    // Uninterpreted functions only does not
//    // need to associate interpreted atoms to
//    // a particular theory solver
//    if ( config.logic != QF_UF )
//    {
////      bool unassigned_atom = e->isLeq( );  // Arithmetic should be assigned
//
//      for ( unsigned i = 1 
//	  ; i < tsolvers.size( ) && status == l_Undef 
//	  ; ++ i )
//      {
//	if ( tsolvers[ i ]->belongsToT( e ) )
//	{
//	  status = tsolvers[ i ]->inform( e );
//	  id_to_belong_mask[ e->getId( ) ] |= SETBIT( i );
//	  unassigned_atom = false;
//	}
//      }
//
//      if ( unassigned_atom )
//	opensmt_error2( e, " cannot be handled by any TSolver. Did you disable some solver in the configure file ?" );
//    }
//
//    informed[ en_e.getId( ) ] = status;
//  }
//  else
//  {
//    status = it->second;
//  }
//
//  return status;
//}

//
// Initialize congruence
//
//void Egraph::initializeCong( ERef e )
//{
//#ifdef PEDANTIC_DEBUG
//  assert( checkInvariants( ) );
//#endif
//
//  assert( e != ERef_Undef );
//  en_e = ea[e];
//  // Skip what is not term or list
//  assert ( en_e.isTerm( ) || en_e.isList( ) );
//  // Skip enil
//  if ( e == ERef_Nil )
//    return;
//  // Skip true and false
//  if ( en_e.isTerm( ) && ( en_e.isTrue( ) || en_e.isFalse( ) ) )
//    return;
//  // Skip already initialized nodes
//  if ( initialized.find( en_e.getId( ) ) != initialized.end( ) )
//    return;
//  // Process arguments first
//  if ( en_e.isList( ) )
//    initializeCong( en_e.getCar( ) );
//  initializeCong( en_e.getCdr( ) );
//  // Precondition
//  assert( en_e.getCar( ) == ea[en_e.getCar( )].getRoot( ) );
//  assert( en_e.getCdr( ) == ea[en_e.getCdr( )]->getRoot( ) );
//  assert( !en_e.hasCongData( ) );
//  e->allocCongData( );
//  // Set constant for constants
//  if ( e->isConstant( ) )
//    e->setConstant( e );
//  // Add parents relationships
//  if ( e->isList( ) )
//    e->getCar( )->addParent( e );
//  e->getCdr( )->addParent( e );
//  // Node initialized
//  initialized.insert( e->getId( ) );
//  // Insert in SigTab
//  if ( config.incremental )
//  {
//    undo_stack_term.push_back( e );
//    undo_stack_oper.push_back( INITCONG );
//
//    Enode * prev = lookupSigTab( e );
//    assert( prev != e );
//    assert( prev == NULL || prev == prev->getCgPtr( ) );
//    if ( prev == NULL )
//      insertSigTab( e );
//    else
//    {
//      // Set congruence pointer to maintain
//      // invariant of signature table
//      e->setCgPtr( prev );
//      // Add to pending
//      pending.push_back( e );
//      pending.push_back( prev );
//      // Merge
//      const bool res = mergeLoop( NULL );
//      if ( !res )
//	opensmt_error( "unexpected result" );
//    }
//  }
//  else
//  {
//    assert( lookupSigTab( e ) == NULL );
//    insertSigTab( e );
//    assert( lookupSigTab( e ) == e );
//  }
//
//#ifdef PEDANTIC_DEBUG
//  assert( checkParents( e ) );
//  assert( checkInvariants( ) );
//#endif
//}

//
// Asserts a literal
//
//bool Egraph::assertLit_ ( ERef e )
//{
//#if VERBOSE
//  cerr << "========= Asserting: " 
//       << e 
//       << " " 
//       << en_e.getId( ) 
//       << " | "
//       << e->getCar( )->getId( )
//       << ", "
//       << e->getCdr( )->getId( )
//       << " ==================" 
//       << endl;
//#endif
//
//  assert( explanation.empty( ) );
//  assert( theoryInitialized );
//  assert( e->isTAtom( ) );
//  assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
//  assert( e->hasPolarity( ) );
//  assert( e->getPolarity( ) == l_False
//       || e->getPolarity( ) == l_True );
//
//  bool n = e->getPolarity( ) == l_False;
//
//  // cerr << "Asserting: " << (n?"!":" ") << e << endl;
//
//  // e is asserted with the same polarity that
//  // we deduced: we don't add it to the congruence
//  if ( e->isDeduced( )
//    && e->getPolarity( ) == e->getDeduced( ) )
//    return true;
//
//  bool res = true;
//  Enode * s = e;
//  //
//  // Make sure the received node has been
//  // initialized
//  //
//  if ( config.incremental 
//    && initialized.find( e->getId( ) ) == initialized.end( ) )
//    initializeCongInc( e );
//
//  // Assert positive or negative equality
//  if ( e->isEq( ) )
//  {
//    // Has arity 2
//    assert( e->getArity( ) == 2 );
//    Enode * lhs = e->get1st( );
//    Enode * rhs = e->get2nd( );
//
//    // If the polarity of the equality is negative
//    if ( n )
//    {
//      res = assertNEq( lhs, rhs, s );
//
//      /*
//      // Handling arrays
//      if( config.logic == QF_AX )
//      	handleArrayAssertedNEq( lhs, rhs );
//      */
//
//      // Also, assert that e is equivalent to false
//      // to trigger theory-deductions automatically
//      if ( res )
//      {
//	res = assertEq( e, mkFalse( ), s );
//	assert( res );
//      }
//    }
//    // Otherwise the polarity of the equality is positive
//    else
//    {
//      res = assertEq( lhs, rhs, s );
//
//      /*
//      // Handling arrays
//      if( config.logic == QF_AX )
//      	handleArrayAssertedEq( lhs, rhs );
//      */
//
//      // Also, assert that e is equivalent to true
//      // to trigger theory-deductions automatically
//      if ( res )
//      {
//	res = assertEq( e, mkTrue( ), s );
//	assert( res );
//      }
//    }
//  }
//  // Assert an explicit strict inequality which are
//  // (partially) interpreted as negated equalities
//  else if ( n && ( e->isLeq( )) )
//  {
//    // Has arity 2
//    assert( e->getArity( ) == 2 );
//    Enode * lhs = e->get1st( );
//    Enode * rhs = e->get2nd( );
//    res = assertNEq( lhs, rhs, s );
//    //
//    // Also, assert that e is equivalent to false
//    // Notice that it may trigger a conflict, for instance
//    // if we have
//    //
//    // a <= b, a=c
//    //
//    // and we push
//    //
//    // !(c <= b)
//    //
//    // the last was deduced positive in a previous call,
//    // but it can be pushed by BCP negated. This is a little
//    // bit asimmetric w.r.t. equality, but it is the
//    // same for uninterpreted predicates
//    //
//    if ( res )
//      res = assertEq( e, mkFalse( ), s );
//  }
//  // Assert Distinction
//  else if ( e->isDistinct( ) )
//  {
//    if ( n && config.logic == QF_UF )
//      opensmt_error2( "can't handle distincts with negative polarity in QF_UF", "" );
//
//    if ( !n )
//      res = assertDist( e, s );
//  }
//  // Considers <= as uninterpreted if pushed positively
//  else if ( e->isUp   ( )
//         || e->isLeq  ( ))
//  {
//    if ( n )
//      res = assertEq( e, mkFalse( ), s );
//    else
//      res = assertEq( e, mkTrue( ), s );
//  }
//  else if ( e->isCostIncur() || e->isCostBound() )
//  {
//    if ( n )
//      res = assertEq( e, mkFalse( ), s );
//    else
//      res = assertEq( e, mkTrue( ), s );
//  }
//  else
//    opensmt_error2( "can't handle ", e );
//
//  // Cleanup the eq-classes generated during expExplain
//  if ( !res )
//  {
//    conf_index = 0;
//    expCleanup( );
//  }
//
//#ifdef STATISTICS
//  if ( res ) tsolvers_stats[ 0 ]->sat_calls ++;
//  else       tsolvers_stats[ 0 ]->uns_calls ++;
//#endif
//
//  assert( !res || explanation.empty( ) );
//  assert( exp_cleanup.empty( ) );
//
//#ifdef PRODUCE_PROOF
//  if ( !res
//    && config.produce_inter > 0 )
//  {
//    list< Enode * > in_list;
//    // We count interpolants from 1,
//    // hence we set the first nibble
//    // to E=1110 instead of F=1111
//    ipartitions_t mask = -2;
//    for ( unsigned in = 1 ; in < getNofPartitions( ) ; in ++ )
//    {
//      // mask &= ~SETBIT( in );
//      clrbit( mask, in );
//      // Compute intermediate interpolants
//      in_list.push_front( cgraph.getInterpolant( mask ) );
//    }
//    interpolants = cons( in_list );
//    cgraph.clear( );
//  }
//#endif
//
//  if ( !res )
//  {
//#if VERBOSE
//    cerr << "Conflict is: " << endl;
//    for ( size_t i = 0 ; i < explanation.size( ) ; i ++ )
//    {
//      cerr << " "
//	<< (explanation[ i ]->getPolarity( ) == l_False?"!":" ")
//	<< explanation[ i ]
//#ifdef PRODUCE_PROOF
//	<< getIPartitions( explanation[ i ] )
//#endif
//	<< endl;
//    }
//#endif
//  }
//
//  return res;
//}


//bool Egraph::assertLit( Enode * e, bool reason )
//{
//  /*
//  if ( config.verbosity > 3 )
//    cerr << "# Egraph::Asserting Literal: " 
//         << ( e->getPolarity( ) == l_True ? "     " : "(not " )
//         << e
//         << ( e->getPolarity( ) == l_True ? "" : ")" )
//         << endl;
//  */
//
//  congruence_running = true;
//#ifndef SMTCOMP
//  model_computed = false;
//#endif
//  // Node may be new. Inform solvers
//  if ( config.incremental )
//    inform( e );
//
//  // Runtime translation
//  suggestions.clear( );
//
//  // Skip if explicitly set
//  const bool skip_uf = config.uf_disable
//  // Or if during interpolation and theory combination
//  // with arithmetic we get something that is not an equality
//#ifdef PRODUCE_PROOF
//		    || ( config.produce_inter != 0 
//		      && ( config.logic == QF_UFIDL
//			|| config.logic == QF_UFLRA )
//		      && !e->isEq( ) )
//#endif
//		     ;
//
//  bool res = skip_uf ? true : assertLit_( e );
//
//  if ( res )
//  {
//    assert( explanation.empty( ) );
//    // Assert literal in the other theories
//    for ( unsigned i = 1 ; i < tsolvers.size( ) && res ; i ++ )
//    {
//      OrdinaryTSolver & t = *tsolvers[ i ];
//#ifdef STATISTICS
//      TSolverStats & ts = *tsolvers_stats[ i ];
//#endif
//
//      // Skip solver if this atom does not belong to T
//      if ( (id_to_belong_mask[ e->getId( ) ] & SETBIT( i )) == 0)
//	continue;
//
//#ifdef STATISTICS
//      size_t deductions_old = deductions.size( );
//#endif
//
//      res = t.assertLit( e, reason );
//      if ( !res )
//	conf_index = i;
//#ifdef STATISTICS
//      if ( res )
//      {
//	ts.sat_calls ++;
//	ts.deductions_done += deductions.size( ) - deductions_old;
//      }
//      else
//	ts.uns_calls ++;
//#endif
//    }
//  }
//
//  return res;
//}

//
// Checks for consistency in theories
//
bool Egraph::check( bool complete )
{
  bool res = true;

  // Assert literal in the other theories
  for ( uint32_t i = 1 ; i < tsolvers.size_( ) && res ; i ++ )
  {
    OrdinaryTSolver & t = *tsolvers[ i ];
#ifdef STATISTICS
    TSolverStats & ts = *tsolvers_stats[ i ];
#endif

#ifdef STATISTICS
    size_t deductions_old = deductions.size( );
#endif

    res = t.check( complete );
    if ( !res ) conf_index = i;

#ifdef STATISTICS
    if ( res )
    {
      ts.sat_calls ++;
      ts.deductions_done += deductions.size( ) - deductions_old;
    }
    else
      ts.uns_calls ++;
#endif
  }

  assert( !res || explanation.size() == 0 );
  assert( exp_cleanup.size() == 0 );

  return res;
}

//
// Pushes a backtrack point
//
void Egraph::pushBacktrackPoint( )
{
  // Save solver state if required
  assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
  backtrack_points.push_back( undo_stack_term.size( ) );

  // Push ordinary theories
  for ( uint32_t i = 1 ; i < tsolvers.size_( ) ; i ++ )
    tsolvers[ i ]->pushBacktrackPoint( );

  deductions_lim .push( deductions.size( ) );
  deductions_last.push( deductions_next );
  assert( deductions_last.size( ) == deductions_lim.size( ) );
}

//
// Pops a backtrack point
//
void Egraph::popBacktrackPoint( )
{
  assert( backtrack_points.size( ) > 0 );
  size_t undo_stack_new_size = backtrack_points.back( );
  backtrack_points.pop_back( );
  backtrackToStackSize( undo_stack_new_size );

  // Pop ordinary theories
  for ( uint32_t i = 1 ; i < tsolvers.size_( ) ; i ++ )
    tsolvers[ i ]->popBacktrackPoint( );

  assert( deductions_last.size( ) > 0 );
  assert( deductions_lim.size( ) > 0 );
  // Restore deduction next
  deductions_next = deductions_last.last();
  deductions_last.pop();
  // Restore deductions
  size_t new_deductions_size = deductions_lim.last( );
  deductions_lim.pop( );
  while( deductions.size_() > new_deductions_size )
  {
    ERef e = deductions.last();
    Enode& en_e = enode_store[e];
    assert( en_e.isDeduced( ) );
    en_e.rsDeduced();
    deductions.pop();
  }
  assert( deductions_next <= deductions.size_() );
  assert( deductions_last.size( ) == deductions_lim.size( ) );
}

//
// Returns a deduction
//
ERef Egraph::getDeduction( )
{
  // Communicate UF deductions
  while ( deductions_next < deductions.size_( ) )
  {
    ERef e = deductions[ deductions_next++ ];
    Enode& en_e = enode_store[e];
    // For sure this has a deduced polarity
    assert( en_e.isDeduced( ) );
    // If it has been pushed it is not a good candidate
    // for deduction
    if ( en_e.hasPolarity( ) )
      continue;

#ifdef STATISTICS
//    const int index = e->getDedIndex( );
//    tsolvers_stats[ index ]->deductions_sent ++;
#endif

    return e;
  }

  // We have already returned all the possible deductions
  return ERef_Undef;
}

//
// Returns a suggestion
//
ERef Egraph::getSuggestion( )
{
  // Communicate suggestion
  while ( !suggestions.size() == 0 )
  {
    ERef e = suggestions.last();
    suggestions.pop();
    Enode& en_e = enode_store[e];
    if ( en_e.hasPolarity( ) )
      continue;
    if ( en_e.isDeduced( ) )
      continue;

    return e;
  }

  // We have already returned all
  // the possible suggestions
  return ERef_Undef;
}

//
// Communicate conflict
//
vec<ERef>& Egraph::getConflict( bool deduction )
{
  assert( 0 <= conf_index && conf_index < (int)tsolvers.size( ) );
  (void)deduction;
#ifdef STATISTICS
  TSolverStats & ts = *tsolvers_stats[ conf_index ];
  if ( deduction )
  {
    if ( (long)explanation.size( ) > ts.max_reas_size )
      ts.max_reas_size = explanation.size( );
    if ( (long)explanation.size( ) < ts.min_reas_size )
      ts.min_reas_size = explanation.size( );
    ts.reasons_sent ++;
    ts.avg_reas_size += explanation.size( );
  }
  else
  {
    if ( (long)explanation.size( ) > ts.max_conf_size )
      ts.max_conf_size = explanation.size( );
    if ( (long)explanation.size( ) < ts.min_conf_size )
      ts.min_conf_size = explanation.size( );
    ts.conflicts_sent ++;
    ts.avg_conf_size += explanation.size( );
  }
#endif
  return explanation;
}

#ifdef PRODUCE_PROOF
Enode * Egraph::getInterpolants( logic_t & l )
{
  assert( config.produce_inter );
  assert( 0 <= conf_index && conf_index < (int)tsolvers.size( ) );
  if ( conf_index == 0 ) 
  {
    l = QF_UF;
    return interpolants;
  }
  return tsolvers[ conf_index ]->getInterpolants( l );
}
#endif

//void Egraph::initializeTheorySolvers( SimpSMTSolver * s )
//{
//  setSolver( s );
//  assert( !theoryInitialized );
//
//  theoryInitialized = true;
//
//  // Reserve empty space
//  tsolvers      .push_back( NULL );
//#ifdef STATISTICS
//  tsolvers_stats.push_back( new TSolverStats( ) );
//#endif
//
//  // No need to instantiate any other solver
//  if ( config.logic == QF_UF )
//    return;
//  // Empty theory solver, a template for user-defined solvers
//  if ( config.logic == EMPTY )
//  {
//    cerr << "# WARNING: Empty solver activated" << endl;
//    tsolvers      .push_back( new EmptySolver( tsolvers.size( ), "Empty Solver", config, *this, sort_store, explanation, deductions, suggestions ) );
//#ifdef STATISTICS
//    tsolvers_stats.push_back( new TSolverStats( ) );
//#endif
//  }
//  else if ( config.logic == QF_BV )
//  {
//    if ( !config.bv_disable )
//    {
//      tsolvers      .push_back( new BVSolver( tsolvers.size( ), "BV Solver", config, *this, sort_store, explanation, deductions, suggestions ) );
//#ifdef STATISTICS
//      tsolvers_stats.push_back( new TSolverStats( ) );
//#endif
//    }
//  }
//  else if ( config.logic == QF_RDL
//         || config.logic == QF_IDL
//         || config.logic == QF_UFIDL )
//  {
//    if ( !config.dl_disable )
//    {
//      if ( getUseGmp( ) )
//	tsolvers    .push_back( new DLSolver<Real>( tsolvers.size( ), "DL Solver", config, *this, sort_store, explanation, deductions, suggestions ) );
//      else
//	tsolvers    .push_back( new DLSolver<long>( tsolvers.size( ), "DL Solver", config, *this, sort_store, explanation, deductions, suggestions ) );
//#ifdef STATISTICS
//      tsolvers_stats.push_back( new TSolverStats( ) );
//#endif
//    }
//  }
//  else if ( config.logic == QF_LRA
//         || config.logic == QF_UFLRA )
//  {
//    if ( !config.lra_disable )
//    {
//      tsolvers      .push_back( new LRASolver( tsolvers.size( ), "LRA Solver", config, *this, sort_store, explanation, deductions, suggestions ) );
//#ifdef STATISTICS
//      tsolvers_stats.push_back( new TSolverStats( ) );
//#endif
//    }
//  }
//  else if ( config.logic == QF_LIA)
//  {
//    if ( !config.lra_disable && config.lra_integer_solver==1 )
//    {
//      tsolvers      .push_back( new LRASolver( tsolvers.size( ), "LIA Solver", config, *this, sort_store, explanation, deductions, suggestions ) );
//#ifdef STATISTICS
//      tsolvers_stats.push_back( new TSolverStats( ) );
//#endif
//    }
//  }
//  else if ( config.logic == QF_CT )
//  {
//    // Allocating a cost solver (we always do this, unless in QF_UF)
//    tsolvers.push_back( new CostSolver( tsolvers.size( ), "Cost Solver", config, *this, sort_store, explanation, deductions, suggestions ) );
//#ifdef STATISTICS
//    tsolvers_stats.push_back( new TSolverStats( ) );
//#endif
//  }
//  else if ( config.logic == QF_AX 
//         || config.logic == QF_AXDIFF )
//  {
//    // Allocating a cost solver (we always do this, unless in QF_UF)
//    tsolvers.push_back( new AXDiffSolver( tsolvers.size( )
//	                                , "AX Diff Solver"
//					, config
//					, *this
//					, sort_store
//					, explanation
//					, deductions
//					, suggestions ) );
//#ifdef STATISTICS
//    tsolvers_stats.push_back( new TSolverStats( ) );
//#endif
//  }
//  else if ( config.logic == QF_BOOL )
//    ; // Do nothing
//  // DO NOT REMOVE THIS COMMENT !!
//  // IT IS USED BY CREATE_THEORY.SH SCRIPT !!
//  // NEW_THEORY_INIT
//  else
//  {
//#ifndef SMTCOMP
//    cerr << "# WARNING: Running in INCOMPLETE mode" << endl;
//#endif
//  }
//
//#ifdef STATISTICS
//  assert( tsolvers.size( ) == tsolvers_stats.size( ) );
//#endif
//}

#ifndef SMTCOMP
//void Egraph::computeModel( )
//{
//  model_computed = true;
//  //
//  // Compute models in tsolvers
//  //
//  for( unsigned i = 1 ; i < tsolvers.size( ) ; i ++ )
//    tsolvers[ i ]->computeModel( );
//  //
//  // Compute values for variables removed
//  // during preprocessing, starting from
//  // the last
//  //
//  for ( int i = top_level_substs.size( ) - 1 ; i >= 0 ; i -- )
//  {
//    Enode * var = top_level_substs[i].first;
//    Enode * term = top_level_substs[i].second;
//    Real r;
//    // Compute value for term
//    evaluateTerm( term, r );
//    // Set value for variable
//    var->setValue( r );
//  }
//}

//void Egraph::printModel( ostream & os )
//{
//  assert( config.produce_models );
//  computeModel( );
//  //
//  // Print values
//  //
//  for( set< Enode * >::iterator it = variables.begin( )
//      ; it != variables.end( )
//      ; it ++ )
//  {
//    // Retrieve enode
//    Enode * v = *it;
//    // Print depending on type
//    if ( v->hasSortBool( ) )
//      continue;
//    else if ( v->hasSortInt( )
//	   || v->hasSortReal( ) )
//    {
//      os << "(= " << v << " ";
//      if ( v->hasValue( ) )
//	os << v->getValue( );
//      else
//	os << "?";
//      os << ")";
//    }
//    else if ( config.logic == QF_UF )
//    {
//      os << "(= " << v << " " << v->getRoot( ) << ")";
//    }
//    else if ( config.logic == QF_CT )
//    {
//      os << "(= " << v << " " << v->getValue( ) << ")";
//    }
//    else
//    {
//      opensmt_error2( "model printing unsupported for this variable: ", v );
//    }
//
//    os << endl;
//  }
//}
#endif

lbool Egraph::addEquality(PTRef term, bool val) {
    term_store.printTerm(term);
    Pterm& t = term_store[term];
    assert( logic.isEquality(t.symb()) );
    // In general we don't want to put the Boolean equalities to UF
    // solver.  However, the Boolean uninterpreted functions are an
    // exception.
//    assert( sym_store[t.symb()][0] != logic.getSort_bool() );

    vec<PTRef> queue;
    queue.push(t[0]);
    queue.push(t[1]);
    vec<PTRef> to_process;

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        queue.pop();
        to_process.push(tr);
        Pterm& tm = term_store[tr];
        for (int i = 0; i < tm.size(); i++)
            queue.push(tm[i]);
    }


    // construct an enode term for each term in to_process
    for (int i = to_process.size() - 1; i >= 0; i--) {
        PTRef tr = to_process[i];
        Pterm& tm = term_store[tr];
        if (!enode_store.termToERef.contains(tr)) {
            ERef sym = enode_store.addSymb(tm.symb());
            ERef cdr = ERef_Nil;
            for (int j = tm.size()-1; j >= 0; j--) {
                ERef car = enode_store.termToERef[tm[j]];
                cdr = enode_store.cons(car, cdr);
            }
            enode_store.addTerm(sym, cdr, tr);
        }
    }

    // Get the lhs and rhs of the equality
    ERef eq_lhs = enode_store.termToERef[t[0]];
    ERef eq_rhs = enode_store.termToERef[t[1]];

    bool rval;
    if (val == true)
        rval = assertEq( eq_lhs, eq_rhs, term );
    else
        rval = assertNEq( eq_lhs, eq_rhs, term);

    return rval == false ? l_False : l_Undef;
}

//===========================================================================
// Private Routines for Core Theory Solver

//
// Assert an equality between nodes x and y
//
bool Egraph::assertEq ( ERef x, ERef y, PTRef r )
{
    Enode& en_x = enode_store[x];
    Enode& en_y = enode_store[x];
    assert( en_x.isTerm() );
    assert( en_y.isTerm() );
    assert( pending.size() == 0 );
//    assert( x->isAtom( )
//         || config.logic != QF_BV
//         || x->getWidth( ) == y->getWidth( ) );

    pending.push( x );
    pending.push( y );

    const bool res = mergeLoop( r );

    return res;
}

//
// Merge what is in pending and propagate to parents
//
bool Egraph::mergeLoop( PTRef reason )
{
//    bool congruence_pending = false;

    while ( pending.size() != 0 )
    {
      // Remove a pending equivalence
      assert( pending.size( ) >= 2 );
      assert( pending.size( ) % 2 == 0 );
      ERef p = pending.last( ); pending.pop( );
      ERef q = pending.last( ); pending.pop( );
      Enode& en_p = enode_store[p];
      Enode& en_q = enode_store[q];

      if ( en_p.getRoot( ) == en_q.getRoot( ) )
        continue;

      // Store explanation, for either congruence or eq
      // The third argument is the reason for the merge
      // of p and q; they may merge because of an equality,
      // and in that case the reason is the id of the equality.
      // Or they may merge because of congruence, and in that
      // case the reason is empty (NULL). Notice that we store
      // reasons only among TERMs, and never among LISTs. That
      // means that the reason for p and q being equal has to
      // be found recursively in their arguments. We store the
      // reason even in case of unmergability, to have an
      // automatic way of retrieving a conflict

//      if ( en_p.isTerm( ) )
//        expStoreExplanation( p, q, congruence_pending ? ERef_Undef : r );

      // Check if they can't be merged
      PTRef reason = PTRef_Undef;
      PTRef* reason_p = &reason;
      bool res = unmergeable( en_p.getRoot(), en_q.getRoot(), reason_p );

      // They are not unmergable, so they can be merged
      if ( !res )
      {
        merge( en_p.getRoot( ), en_q.getRoot( ) );
//        congruence_pending = true;
        continue;
      }

      // Conflict detected. We should retrieve the explanation
      // We have to distinguish 2 cases. If the reason for the
      // conflict is ERef_Undef, it means that a conflict arises because
      // we tried to merge two classes that are assigned to different
      // constants, otherwise we have a proper reason
      ERef reason_1 = ERef_Undef;
      ERef reason_2 = ERef_Undef;
      //
      // Different constants
      //
      ERef enr_proot = en_p.getRoot();
      ERef enr_qroot = en_q.getRoot();

      if ( reason == PTRef_Undef )
      {
          Enode& en_proot = enode_store[enr_proot];
          Enode& en_qroot = enode_store[enr_qroot];

          assert( sym_store[en_proot.getTerm()].isConstant() );
          assert( sym_store[en_qroot.getTerm()].isConstant() );

          assert( en_proot.getTerm() != en_qroot.getTerm() );
  #ifdef PRODUCE_PROOF
          if ( config.produce_inter > 0 )
          {
              cgraph.setConf( p->getRoot( )->getConstant( )
                        , q->getRoot( )->getConstant( )
                        , NULL );
          }
  #endif
          //
          // We need explaining
          //
          // 1. why p and p->constant are equal
          exp_pending.push( p );
          exp_pending.push( en_proot.getTerm() );
          // 2. why q and q->constant are equal
          exp_pending.push( q );
          exp_pending.push( en_qroot.getTerm() );
          // 3. why p and q are equal
          exp_pending.push( q );
          exp_pending.push( p );

          initDup1( );
//          expExplain( );
          doneDup1( );
      }
      // Does the reason term correspond to disequality symbol
      else if ( logic.isDisequality(term_store[reason].symb()) ) {
          // The reason is a distinction
          explanation.push( reason );
          // We should iterate through the elements
          // of the distinction and find which atoms
          // are causing the conflict
          Pterm& pt_reason = term_store[reason];
          for (int i = 0; i < pt_reason.size(); i++) {
              // (1) Get the proper term reference from pos i in the distinction
              // (2) Get the enode corresponding to the proper term
              // (3) Find the enode corresponding to the root
              // (4) Check if the root enode is the same as the root of p or q

              PTRef ptr_arg = pt_reason[i];                             // (1)
              ERef  enr_arg = enode_store.termToERef[ptr_arg];          // (2)
              ERef  enr_arg_root = enode_store[enr_arg].getRoot();     // (3)

              // (4)
              if ( enr_arg_root == enr_proot ) { assert( reason_1 == ERef_Undef ); reason_1 = enr_arg; }
              if ( enr_arg_root == enr_qroot ) { assert( reason_2 == ERef_Undef ); reason_2 = enr_arg; }
          }
          assert( reason_1 != ERef_Undef );
          assert( reason_2 != ERef_Undef );
//          expExplain( reason_1, reason_2, reason );
      }
      else {
        // The reason is a negated equality
        Pterm& pt_reason = term_store[reason];
        assert( logic.isEquality(pt_reason.symb())
//             || reason->isLeq( )
             );

          // Hmm, the difference being?
//          if ( config.incremental ) {
//              Enode * s = reason;
//              explanation.push_back( s );
//          }
//          else
//              explanation.push_back( reason );

          explanation.push(reason);

          // The equality
          // If properly booleanized, the left and righ sides of equality
          // will always be UF terms
          // The left hand side of the equality
          reason_1 = enode_store.termToERef[pt_reason[0]];
          // The rhs of the equality
          reason_2 = enode_store.termToERef[pt_reason[1]];
//          reason_1 = enode_store.termToERef[pt_reason[0]];
//          reason_2 = enode_store.termToERef[pt_reason[1]];

          assert( reason_1 != PTRef_Undef );
          assert( reason_2 != PTRef_Undef );

#if VERBOSE
          cerr << "Reason is neg equality: " << reason << endl;
#endif

//          expExplain( reason_1, reason_2, reason );
      }

      // Clear remaining pendings
      pending.clear( );
      // Remove the last explanation that links
      // the two unmergable classes
//      expRemoveExplanation( );
      // Return conflict
      return false;
    }

    return true;
}

//
// Assert a disequality between nodes x and y
//
bool Egraph::assertNEq ( ERef x, ERef y, PTRef r )
{
#if MORE_DEDUCTIONS
  neq_list.push_back( r );
  undo_stack_oper.push_back( ASSERT_NEQ );
  undo_stack_term.push_back( r );
#endif

  ERef p = enode_store[x].getRoot( );
  ERef q = enode_store[y].getRoot( );

  // They can't be different if the nodes are in the same class
  if ( p == q )
  {
    explanation.push( r );
//    expExplain( x, y, r );

#ifdef PEDANTIC_DEBUG
    assert( checkExp( ) );
#endif
    return false;
  }

  // Is it possible that x is already in the list of y
  // and viceversa ? YES. If things have
  // been done carefully (for instance, if x=y is the same atom
  // as y=x), each theory atom appears only once in the trail.
  // However it is possible to get x!=y and x<y, and pushing
  // x<y is the same as x!=y for the UF solver. However, I don't
  // think this is going to be a big performance problem, worst
  // case it doubles the size of forbid lists. But checking the
  // lists for duplicates every time would be time-consuming,
  // especially when we have many !='s. For now I'll leave it
  // unchecked.

  // Create new distinction in q
  ELRef pdist = forbid_allocator.alloc(p, r);
  Enode& en_q = enode_store[q];
  // If there is no node in forbid list
  if ( en_q.getForbid() == ELRef_Undef )
  {
    en_q.setForbid( pdist );
    forbid_allocator[pdist].link = pdist;
  }
  // Otherwise we should put the new node after the first
  // and make the first point to pdist. This is because
  // the list is circular, but could be emptq. Therefore
  // we need a "reference" element for keeping it circular.
  // So the last insertion is either the second element or
  // the only present in the list
  else
  {
    forbid_allocator[pdist].link = forbid_allocator[en_q.getForbid()].link;
    forbid_allocator[en_q.getForbid()].link = pdist;
  }

  // Create new distinction in p
  ELRef qdist = forbid_allocator.alloc(q, r);
  Enode& en_p = enode_store[p];
  if ( en_p.getForbid() == ELRef_Undef )
  {
    en_p.setForbid( qdist );
    forbid_allocator[qdist].link = qdist;
  }
  // Same arguments above
  else
  {
    Elist& forb_p = forbid_allocator[en_p.getForbid()];
    forbid_allocator[qdist].link = forb_p.link;
    forb_p.link = qdist;
  }

  // Save operation in undo_stack
  assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
  undo_stack_oper.push( DISEQ );
  undo_stack_term.push( q );

  return true;
}

bool Egraph::assertDist( ERef d, ERef r )
{
    Enode& en_d = enode_store[d];
    // Retrieve distinction number
    size_t index = en_d.getDistIndex();
    // While asserting, check that no two nodes are congruent
    Map< enodeid_t, ERef, EnodeIdHash, Equal<enodeid_t> > root_to_enode;
    // Nodes changed
    vec<ERef> nodes_changed;
    // Assign distinction flag to all arguments
    ERef list = en_d.getCdr();
    while (list != ERef_Nil) {
        ERef e = enode_store[list].getCar( );
        Enode& en_e = enode_store[e];

//        pair< map< enodeid_t, Enode * >::iterator, bool > elem = root_to_enode.insert( make_pair( e->getRoot( )->getId( ), e ) );
        enodeid_t root_id = enode_store[en_e.getRoot()].getId();
        if ( root_to_enode.contains(root_id) ) {
            // Two equivalent nodes in the same distinction. Conflict
            explanation.push(r);
            // Extract the other node with the same root
            ERef p = root_to_enode[root_id];
            // Check condition
            assert( enode_store[p].getRoot() == en_e.getRoot() );
            // Retrieve explanation
//            expExplain( e, p, r );
            // Revert changes, as the current context is inconsistent
            while( nodes_changed.size() != 0 ) {
                ERef n = nodes_changed.last();
                nodes_changed.pop();
                // Deactivate distinction in n
                Enode& en_n = enode_store[n];
                en_n.setDistClasses( en_n.getDistClasses() & ~(SETBIT( index )) );
            }
            return false;
        }
        // Activate distinction in e
        en_e.setDistClasses( (en_e.getDistClasses( ) | SETBIT( index )) );
        nodes_changed.push(e);
        // Next elem
        list = enode_store[list].getCdr();
    }
    // Distinction pushed without conflict
    assert( undo_stack_oper.size() == undo_stack_term.size() );
    undo_stack_oper.push(DIST);
    undo_stack_term.push(d);
    return true;
}

//
// Backtracks stack to a certain size
//
void Egraph::backtrackToStackSize ( size_t size )
{
  // Make sure explanation is cleared
  // (might be empty, though, if boolean backtracking happens)
  // explanation.clear( );
  //
  // Restore state at previous backtrack point
  //
  while ( undo_stack_term.size_() > size )
  {
    oper_t last_action = undo_stack_oper.last();
    ERef e = undo_stack_term.last();
    Enode& en_e = enode_store[e];

    undo_stack_oper.pop();
    undo_stack_term.pop();

    if ( last_action == MERGE )
    {
      undoMerge( e );
      if ( en_e.isTerm( ) ) {
//	expRemoveExplanation( );
      }
    }
#if MORE_DEDUCTIONS
    else if ( last_action == ASSERT_NEQ )
    {
      assert( neq_list.last( ) == e );
      neq_list.pop( );
    }
#endif
    else if ( last_action == INITCONG )
    {
      assert( config.isIncremental() );
#if VERBOSE
      cerr << "UNDO: BEG INITCONG " << e << endl;
#endif
      ERef car = en_e.getCar( );
      ERef cdr = en_e.getCdr( );
      assert( car != ERef_Undef );
      assert( cdr != ERef_Undef );

      if ( en_e.getCgPtr( ) == e )
      {
        assert( enode_store.lookupSig( e ) == e );
        // Remove from sig_tab
        enode_store.removeSig( e );
      }
      else
      {
        assert( enode_store.lookupSig( e ) != e );
        en_e.setCgPtr( e );
      }

      assert( initialized.find( en_e.getId( ) ) != initialized.end( ) );
      // Remove from initialized nodes
      initialized.erase( en_e.getId( ) );
      assert( initialized.find( en_e.getId( ) ) == initialized.end( ) );
      // Remove parents info
      if ( en_e.isList( ) )
        enode_store.removeParent( car, e );
      enode_store.removeParent( cdr, e );

      // Deallocate congruence data
      // This sounds like a huge overhead!
//      assert( en_e.hasCongData( ) );
//      e->deallocCongData( );
//      assert( !e->hasCongData( ) );
    }
    else if ( last_action == FAKE_MERGE )
    {
#if VERBOSE
      cerr << "UNDO: BEGIN FAKE MERGE " << e << endl;
#endif
      assert( initialized.find( en_e.getId( ) ) != initialized.end( ) );
      initialized.erase( en_e.getId( ) );
      assert( initialized.find( en_e.getId( ) ) == initialized.end( ) );
//      assert( e->hasCongData( ) );
//      e->deallocCongData( );
//      assert( !e->hasCongData( ) );
    }
    else if ( last_action == FAKE_INSERT )
    {
#if VERBOSE
      cerr << "UNDO: BEGIN FAKE INSERT " << e << endl;
#endif
      assert( en_e.isTerm( ) || en_e.isList( ) );
      ERef car = en_e.getCar( );
      ERef cdr = en_e.getCdr( );
      assert( car );
      assert( cdr );

      // Node must be there if its a congruence
      // root and it has to be removed
      if ( en_e.getCgPtr() == e )
      {
        assert( enode_store.lookupSig( e ) == e );
        enode_store.removeSig( e );
      }
      // Otherwise sets it back to itself
      else
      {
        assert( enode_store.lookupSig( e ) != e );
        en_e.setCgPtr( e );
      }

      // Remove Parent info
      if ( en_e.isList( ) )
        enode_store.removeParent( car, e );
      enode_store.removeParent( cdr, e );
      // Remove initialization
      assert( initialized.find( en_e.getId( ) ) != initialized.end( ) );
      initialized.erase( en_e.getId( ) );
      // Dealloc cong data
//      assert( e->hasCongData( ) );
//      e->deallocCongData( );
//      assert( !e->hasCongData( ) );
    }
    else if ( last_action == DISEQ )
      undoDisequality( e );
    else if ( last_action == DIST )
      undoDistinction( e );
//    else if ( last_action == SYMB )
//      removeSymbol( e );
//    else if ( last_action == NUMB )
//      removeNumber( e );
    else if ( last_action == CONS )
//      undoCons( e );
//    else if ( last_action == INSERT_STORE )
//      removeStore( e );
        ;
    else
      opensmt_error( "unknown action" );
  }

  assert( undo_stack_term.size( ) == undo_stack_oper.size( ) );
}

// bool Egraph::checkDupClause( Enode * c1, Enode * c2 )
// {
//   assert( c1 );
//   assert( c2 );
//   // Swap let cl3 be the lowest clause
//   if ( c1->getId( ) > c2->getId( ) )
//   {
//     Enode * tmp = c1;
//     c1 = c2;
//     c2 = tmp;
//   }
// 
// #ifdef BUILD_64
//   enodeid_pair_t sig = encode( c1->getId( ), c2->getId( ) );
// #else
//   Pair( enodeid_t ) sig = make_pair( c1->getId( ), c2->getId( ) );
// #endif
// 
//   const bool res = clauses_sent.insert( sig ).second == false;
//   return res;
// }

//void Egraph::splitOnDemand( vector< Enode * > & c, const int
//#ifdef STATISTICS
//    id 
//#endif
//    )
//{
//  assert( config.incremental );
//  // Assume that we split only of size 2
//  assert( c.size( ) == 2 );
//  if ( checkDupClause( c[ 0 ], c[ 1 ] ) ) return;
//#ifdef STATISTICS
//  assert( id >= 0 );
//  assert( id < static_cast< int >( tsolvers_stats.size( ) ) );
//  TSolverStats & ts = *tsolvers_stats[ id ];
//  if ( (long)c.size( ) > ts.max_sod_size )
//    ts.max_sod_size = c.size( );
//  if ( (long)c.size( ) < ts.min_sod_size )
//    ts.min_sod_size = c.size( );
//  ts.sod_sent ++;
//  ts.sod_done ++;
//  ts.avg_sod_size += c.size( );
//#endif
//
//#ifdef PRODUCE_PROOF
//  assert( config.produce_inter == 0 || c[ 0 ]->getIPartitions( ) != 0 );
//  assert( config.produce_inter == 0 || c[ 1 ]->getIPartitions( ) != 0 );
//  // FIXME: should compute interpolant ...
//  solver->addSMTAxiomClause( c, NULL );
//#else
//  solver->addSMTAxiomClause( c );
//#endif
//}

//void Egraph::splitOnDemand( Enode * c, const int
//#ifdef STATISTICS
//    id 
//#endif
//    )
//{
//  assert( c );
//
//#ifdef STATISTICS
//  assert( id >= 0 );
//  assert( id < static_cast< int >( tsolvers_stats.size( ) ) );
//  TSolverStats & ts = *tsolvers_stats[ id ];
//  if ( ts.max_sod_size < 1 )
//    ts.max_sod_size = 1;
//  if ( ts.min_sod_size > 1 )
//    ts.min_sod_size = 1;
//  ts.sod_sent ++;
//  ts.sod_done ++;
//  ts.avg_sod_size ++;
//#endif
//
//  solver->addNewAtom( c );
//}

//=============================================================================
// Congruence Closure Routines

//
// Merge the class of x with the class of y
// x will become the representant
//
void Egraph::merge ( ERef x, ERef y )
{
#ifdef PEDANTIC_DEBUG
    assert( checkParents( x ) );
    assert( checkParents( y ) );
    assert( checkInvariants( ) );
#endif

    // This is weird.  If I get the references here and change them afterwards, the cgdata will not be correct.
//    Enode& en_x = enode_store[x];
//    Enode& en_y = enode_store[y];

//    assert( !en_x.isConstant( ) || !en_y.isConstant( ) );
//    assert( !en_x.isConstant( ) || en_x.getSize( ) == 1 );
//    assert( !y->isConstant( ) || y->getSize( ) == 1 );
    assert( enode_store[x].getRoot( ) != enode_store[y].getRoot( ) );
    assert( x == enode_store[x].getRoot( ) );
    assert( y == enode_store[y].getRoot( ) );

  // Swap x,y if y has a larger eq class
    if ( enode_store[x].getSize( ) < enode_store[y].getSize( ) )
//    || en_x.isConstant( ) )
    {
        ERef tmp = x;
        x = y;
        y = tmp;
    }
        // Get the references right here
    Enode& en_x = enode_store[x];
    Enode& en_y = enode_store[y];

//    assert( !x->isConstant( ) );

  // TODO:
  // Propagate equalities to other ordinary theories
  //

  // Update forbid list for x by adding elements of y
    if ( en_y.getForbid( ) != ELRef_Undef ) {
        // We assign the same forbid list
        if ( en_x.getForbid( ) == ELRef_Undef )
            en_x.setForbid( en_y.getForbid( ) );
        // Otherwise we splice the two lists
        else {
            ELRef tmp = forbid_allocator[en_x.getForbid()].link;
            forbid_allocator[en_x.getForbid()].link = forbid_allocator[en_y.getForbid()].link;
            forbid_allocator[en_y.getForbid()].link = tmp;
        }
    }

    // Merge distinction classes
    en_x.setDistClasses( ( en_x.getDistClasses( ) | en_y.getDistClasses( ) ) );
    // Assign w to the class with fewer parents
    ERef w = en_x.getParentSize() < en_y.getParentSize( ) ? x : y ;
    // Visit each parent of w, according to the type of w
    // and remove each congruence root from the signature table
    Enode& en_w = enode_store[w];
    ERef p = en_w.getParent();
    const ERef pstart = p;
    const bool scdr = en_w.isList( );
    for ( ; p != ERef_Undef ; ) {
        Enode& en_p = enode_store[p];
        assert ( en_p.isTerm( ) || en_p.isList( ) );
        // If p is a congruence root
        if ( p == en_p.getCgPtr( ) )
            enode_store.removeSig( p );
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar( ) ;
        // End of cycle
        if ( p == pstart )
            p = ERef_Undef;
    }

    // Compute deductions that follows from
    // merging x and y. Probably this function
    // could be partially embedded into the next
    // cycle. However, for the sake of simplicity
    // we prefer to separate the two contexts
    if ( config.uf_theory_propagation > 0 ) {
//        deduce( x, y );
    }

    // Perform the union of the two equivalence classes
    // i.e. reroot every node in y's class to point to x

    ERef v = y;
    const ERef vstart = v;
    for (;;) {
        Enode& en_v = enode_store[v];
        en_v.setRoot(x);
        v = en_v.getNext();
        if (v == vstart)
            break;
    }

    // Splice next lists
    ERef tmp = en_x.getNext();
    en_x.setNext( en_y.getNext() );
    en_y.setNext( tmp );
    // Update size of the congruence class
    en_x.setSize( en_x.getSize( ) + en_y.getSize( ) );

    // Preserve signatures of larger parent set
    if ( en_x.getParentSize() < en_y.getParentSize() )
    {
        enodeid_t tmp = en_x.getCid();
        en_x.setCid( en_y.getCid() );
        en_y.setCid( tmp );
    }

    // Insert new signatures and propagate congruences
    p = en_w.getParent();
    for ( ; p != ERef_Undef; ) {
        Enode& en_p = enode_store[p];
        // If p is a congruence root
        if ( p == en_p.getCgPtr( ) ) {
            //ERef q = EnodeStore.insertSig(p);
            // Signature already present
            //if ( q != p )
            if (enode_store.containsSig(p)) {
                ERef q = enode_store.lookupSig(p);
                en_p.setCgPtr( q );
                pending.push( p );
                pending.push( q );
            }
            else enode_store.insertSig(p);
        }
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar( ) ;
        // Exit if cycle complete
        if ( p == pstart )
            p = ERef_Undef;
    }

    // Merge parent lists
    if ( en_y.getParent() != ERef_Undef ) {
        // If x hasn't got parents, we assign y's one
        if ( en_x.getParent() == ERef_Undef )
            en_x.setParent( en_y.getParent() );
        // Splice the parent lists
        else {
            if ( en_x.isList() ) {
                ERef tmp = enode_store[en_x.getParent()].getSameCdr();
                enode_store[en_x.getParent()].setSameCdr( enode_store[en_y.getParent()].getSameCdr( ) );
                enode_store[en_y.getParent()].setSameCdr( tmp );
            }
            else {
                ERef tmp = enode_store[en_x.getParent()].getSameCar();
                enode_store[en_x.getParent()].setSameCar( enode_store[en_y.getParent()].getSameCar() );
                enode_store[en_y.getParent()].setSameCar( tmp );
            }
        }
    }
    // Adjust parent size
    en_x.setParentSize( en_x.getParentSize( ) + en_y.getParentSize( ) );

    // Store info about the constant
//    if ( en_y.getConstant( ) != E) {
//        assert( en_x.getConstant( ) == NULL );
//        x->setConstant( y->getConstant( ) );
//  }
  // Store info about the constant
//  else if ( x->getConstant( ) != NULL )
//  {
//    assert( y->getConstant( ) == NULL );
//    y->setConstant( x->getConstant( ) );
//  }

  // Push undo record
    assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
    undo_stack_oper.push( MERGE );
    undo_stack_term.push( y );

#ifdef PEDANTIC_DEBUG
    assert( checkParents( x ) );
    assert( checkParents( y ) );
    assert( checkInvariants( ) );
#endif
}

//
// Deduce facts from the merge of x and y
//
//void Egraph::deduce( Enode * x, Enode * y )
//{
//  lbool deduced_polarity = l_Undef;
//
//  if ( x->getConstant( ) == etrue )
//    deduced_polarity = l_True;
//  else if ( x->getConstant( ) == efalse )
//    deduced_polarity = l_False;
//
//  // Let be y store the representant of the class
//  // containing the facts that we are about to deduce
//  if ( deduced_polarity == l_Undef )
//  {
//    Enode * tmp = x;
//    x = y;
//    y = tmp;
//  }
//
//  if ( x->getConstant( ) == etrue )
//    deduced_polarity = l_True;
//  else if ( x->getConstant( ) == efalse )
//    deduced_polarity = l_False;
//
//  if ( deduced_polarity == l_Undef )
//    return;
//
//  Enode * v = y;
//  const Enode * vstart = v;
//  for (;;)
//  {
//    // We deduce only things that aren't currently assigned or
//    // that we previously deduced on this branch
//    Enode * sv = v;
//    if ( !sv->hasPolarity( )
//      && !sv->isDeduced( ) 
//      // Also when incrementality is used, node should be explicitly informed
//      && ( config.incremental == 0 || informed.find( sv->getId( ) ) != informed.end( ) )
//      )
//    {
//      sv->setDeduced( deduced_polarity, id );
//      deductions.push_back( sv );
//#ifdef STATISTICS
//      tsolvers_stats[ 0 ]->deductions_done ++;
//#endif
//    }
//    v = v->getNext( );
//    if ( v == vstart )
//      break;
//  }
//
//#ifdef PEDANTIC_DEBUG
//  assert( checkInvariants( ) );
//#endif
//}

//
// Starts with the E-graph state that existed after the
// pertinent merge and restores the E-graph to the state
// it had before the pertinent merge
//
void Egraph::undoMerge( ERef y )
{
    assert( y != ERef_Undef );

    Enode& en_y = enode_store[y];

    // x is the node that was merged with y
    ERef x = en_y.getRoot( );

    assert( x != ERef_Undef );

    Enode& en_x = enode_store[x];

#if VERBOSE
    cerr << "UM: Undoing merge of " << y << " and " << x << endl;
#endif

    // Undoes the merge of the parent lists
    en_x.setParentSize( en_x.getParentSize() - en_y.getParentSize() );
    // Restore the correct parents
    if ( en_y.getParent( ) != ERef_Undef ) {
        // If the parents are equal, that means that
        // y's parent has been assigned to x
        if ( en_x.getParent( ) == en_y.getParent( ) )
            en_x.setParent( ERef_Undef );
        // Unsplice the parent lists
        else {
            assert( en_x.getParent() != ERef_Undef );
            if ( en_x.isList( ) ) {
                ERef tmp = enode_store[en_x.getParent()].getSameCdr();
                enode_store[en_x.getParent()].setSameCdr( enode_store[en_y.getParent()].getSameCdr() );
                enode_store[en_y.getParent()].setSameCdr( tmp );
            }
            else {
                ERef tmp = enode_store[en_x.getParent()].getSameCar();
                enode_store[en_x.getParent()].setSameCar( enode_store[en_y.getParent()].getSameCar() );
                enode_store[en_y.getParent()].setSameCar( tmp );
            }
        }
    }

    // Assign w to the smallest parent class
    ERef w = en_x.getParentSize( ) < en_y.getParentSize( ) ? x : y ;
    Enode& en_w = enode_store[w];
    // Undoes the insertion of the modified signatures
    ERef p = en_w.getParent( );
    const ERef pstart = p;
    // w might be NULL, i.e. it may not have fathers
    const bool scdr = w == ERef_Undef ? false : en_w.isList( );

    for ( ; p != ERef_Undef ; ) {
        Enode& en_p = enode_store[p];
        assert( en_p.isTerm( ) || en_p.isList( ) );
        // If p is a congruence root
        if ( p == en_p.getCgPtr( ) ) {
            assert( enode_store.lookupSig( p ) != ERef_Undef );
            enode_store.removeSig( p );
        }
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar( ) ;
        // End of cycle
        if ( p == pstart )
            p = ERef_Undef;
    }
    // Restore the size of x's class
    en_x.setSize( en_x.getSize( ) - en_y.getSize( ) );
    // Unsplice next lists
    ERef tmp = en_x.getNext( );
    en_x.setNext( en_y.getNext( ) );
    en_y.setNext( tmp );
    // Reroot each node of y's eq class back to y
    ERef v = y;
    const ERef vstart = v;
    for (;;) {
        Enode& en_v = enode_store[v];
        en_v.setRoot( y );
        v = en_v.getNext( );
        if ( v == vstart )
            break;
    }
    // Undo swapping
    if ( en_x.getParentSize( ) < en_y.getParentSize( ) ) {
        enodeid_t tmp = en_x.getCid( );
        en_x.setCid( en_y.getCid( ) );
        en_y.setCid( tmp );
    }
    // Reinsert back signatures that have been removed during
    // the merge operation
    p = en_w.getParent( );
    for ( ; p != ERef_Undef; ) {
        Enode& en_p = enode_store[p];
        assert( en_p.isTerm( ) || en_p.isList( ) );

        ERef cg = en_p.getCgPtr();
        Enode& en_cg = enode_store[cg];
        // If p is a congruence root
        if ( p == cg
            || enode_store[en_p.getCar()].getRoot() != enode_store[en_cg.getCar()].getRoot()
            || enode_store[en_p.getCdr()].getRoot() != enode_store[en_cg.getCdr()].getRoot() )
        {
            assert(!enode_store.containsSig(p));
            enode_store.insertSig(p);
//      (void)res; // Huh?
//            assert( res == p );
            en_p.setCgPtr( p );
        }
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar();
        // End of cycle
        if ( p == pstart )
        p = ERef_Undef;
    }

    // Restore distinction classes for x, with a set difference operation
    en_x.setDistClasses( ( en_x.getDistClasses() & ~(en_y.getDistClasses())) );

    // Restore forbid list for x and y
    if ( en_x.getForbid( ) == en_y.getForbid( ) )
        en_x.setForbid( ELRef_Undef );
    // Unsplice back the two lists
    else if ( en_y.getForbid( ) != ELRef_Undef ) {
        ELRef tmp = forbid_allocator[en_x.getForbid()].link;
        forbid_allocator[en_x.getForbid()].link = forbid_allocator[en_y.getForbid()].link;
        forbid_allocator[en_y.getForbid()].link = tmp;
    }

//    if ( en_y.getConstant() != NULL )
//  {
//    Enode * yc = y->getConstant( );
//    Enode * xc = x->getConstant( );
//    (void)xc;
//    assert( yc == xc );
    // Invariant: the constant comes from one class only
    // No merge can occur beteween terms that point to the
    // same constant, as they would be in the same class already
//    assert( ( yc->getRoot( ) == y && xc->getRoot( ) != x )
//	 || ( yc->getRoot( ) != y && xc->getRoot( ) == x ) );
    // Determine from which class the constant comes from
//    if ( yc->getRoot( ) == y )
//      x->setConstant( NULL );
//    else
//      y->setConstant( NULL );
//  }

  //
  // TODO: unmerge for ordinary theories
  //

#ifdef PEDANTIC_DEBUG
  assert( checkParents( y ) );
  assert( checkParents( x ) );
  assert( checkInvariants( ) );
#endif
}

//
// Restore the state before the addition of a disequality
//
void Egraph::undoDisequality ( ERef x )
{
    Enode& en_x = enode_store[x];
    assert( en_x.getForbid() != ELRef_Undef );

    // We have to distinct two cases:
    // If there is only one node, that is the
    // distinction to remove
    ELRef xfirst = en_x.getForbid( );
    ERef y = ERef_Undef;
    Elist& el_xfirst = forbid_allocator[xfirst];
    if ( el_xfirst.link == xfirst )
        y = el_xfirst.e;
    else
        y = forbid_allocator[el_xfirst.link].e;

    Enode& en_y = enode_store[y];

    ELRef yfirst = en_y.getForbid();
    // Some checks
    assert( yfirst != ELRef_Undef );
    Elist& el_yfirst = forbid_allocator[yfirst];
    assert( el_yfirst.link != yfirst || el_yfirst.e == x );
    assert( el_yfirst.link == yfirst || forbid_allocator[el_yfirst.link].e == x );
    assert( en_x.getRoot( ) != en_y.getRoot( ) );

    ELRef ydist = el_xfirst.link == xfirst ? xfirst : el_xfirst.link;
    Elist& el_ydist = forbid_allocator[ydist];

    // Only one node in the list
    if ( el_ydist.link == ydist )
        en_x.setForbid( ELRef_Undef );
    // Other nodes in the list
    else
        el_xfirst.link = el_ydist.link;
    forbid_allocator.free(ydist);

    ELRef xdist = el_yfirst.link == yfirst ? yfirst : el_yfirst.link;
    Elist& el_xdist = forbid_allocator[xdist];

    // Only one node in the list
    if ( el_xdist.link == xdist )
    en_y.setForbid( ELRef_Undef );
    // Other nodes in the list
    else
        el_yfirst.link = el_xdist.link;
    forbid_allocator.free(xdist);

#ifdef PEDANTIC_DEBUG
    assert( checkInvariants( ) );
#endif
}

//
// Undoes the effect of pushing a distinction
//
void Egraph::undoDistinction ( ERef r )
{
    // Retrieve distinction index
    Enode& en_r = enode_store[r];
    size_t index = en_r.getDistIndex();
    // Iterate through the list
    ERef list = en_r.getCdr( );
    while ( list != ERef_Nil ) {
        Enode& en_list = enode_store[list];
        ERef e = en_list.getCar();
        Enode& en_e = enode_store[e];
        // Deactivate distinction in e
        en_e.setDistClasses( (en_e.getDistClasses( ) & ~(SETBIT( index ))) );
        // Next elem
        list = en_list.getCdr();
    }

#ifdef PEDANTIC_DEBUG
    assert( checkInvariants( ) );
#endif
}

bool Egraph::unmergeable ( ERef x, ERef y, PTRef* r )
{
    assert( x != ERef_Undef );
    assert( y != ERef_Undef );
    assert( *r == PTRef_Undef );
    ERef p = enode_store[x].getRoot();
    ERef q = enode_store[y].getRoot();
    // If they are in the same class, they can merge
    if ( p == q ) return false;
    // Check if they have different constants. It is sufficient
    // to check that they both have a constant. It is not
    // possible that the constant is the same. In fact if it was
    // the same, they would be in the same class, but they are not

//  if ( p->getConstant( ) != NULL && q->getConstant( ) != NULL ) return true;
    // Check if they are part of the same distinction (general distinction)
    Enode& en_p = enode_store[p];
    Enode& en_q = enode_store[q];
    dist_t intersection = ( en_p.getDistClasses( ) & en_q.getDistClasses( ) );
    if ( intersection ) {
        // Compute the first index in the intersection
        // TODO: Use hacker's delight
        unsigned index = 0;
        while ( ( intersection & 1 ) == 0 ) {
            intersection = intersection >> 1;
            index ++;
        }
        *r = indexToDistReas( index );
        assert( *r != PTRef_Undef );
        return true;
    }
    // Check forbid lists (binary distinction)
    const ELRef pstart = en_p.getForbid( );
    const ELRef qstart = en_q.getForbid( );
    // If at least one is empty, they can merge
    if ( pstart == ELRef_Undef || qstart == ELRef_Undef )
        return false;

    ELRef pptr = pstart;
    ELRef qptr = qstart;

    for (;;) {
        Elist& el_pptr = forbid_allocator[pptr];
        Elist& el_qptr = forbid_allocator[qptr];
        // They are unmergable if they are on the other forbid list
        if ( enode_store[el_pptr.e].getRoot( ) == q ){ *r = el_pptr.reason; return true; }
        if ( enode_store[el_qptr.e].getRoot( ) == p ){ *r = el_qptr.reason; return true; }
        // Pass to the next element
        pptr = el_pptr.link;
        qptr = el_qptr.link;
        // If either list finishes, exit. This is ok because
        // if x is on y's forbid list, then y is on x's forbid
        // list as well
        if ( pptr == pstart ) break;
        if ( qptr == qstart ) break;
    }
    // If here they are mergable
    assert( *r == PTRef_Undef );
    return false;
}

//
// Creates the dynamic version of the enode
//
//void Egraph::initializeCongInc( Enode * top )
//{
//  assert( top );
//  assert( initialized.find( top->getId( ) ) == initialized.end( ) );
//
//  vector< Enode * > unprocessed_enodes;
//  unprocessed_enodes.push_back( top );
//
//  while ( !unprocessed_enodes.empty( ) )
//  {
//    Enode * e = unprocessed_enodes.back( );
//    assert( e );
//    
//    if ( initialized.find( e->getId( ) ) != initialized.end( ) )
//    {
//      unprocessed_enodes.pop_back( );
//      continue;
//    }
//
//    bool unprocessed_children = false;
//    if ( e->getCar( )->isTerm( ) 
//      && initialized.find( e->getCar( )->getId( ) ) == initialized.end( ) )
//    {
//      unprocessed_enodes.push_back( e->getCar( ) );
//      unprocessed_children = true;
//    }
//    if ( !e->getCdr( )->isEnil( ) 
//      && initialized.find( e->getCdr( )->getId( ) ) == initialized.end( ) )
//    {
//      unprocessed_enodes.push_back( e->getCdr( ) );
//      unprocessed_children = true;
//    }
//
//    if ( unprocessed_children )
//      continue;
//
//    unprocessed_enodes.pop_back( );
//    // 
//    // Initialization happens here
//    //
//    assert( e->isTerm( ) || e->isList( ) );
//    assert( !e->isEnil( ) );
//    assert( !e->isTerm( ) || !e->isTrue( ) );
//    assert( !e->isTerm( ) || !e->isFalse( ) );
//    // If it's safe to initialize
//    if ( e->getCar( ) == e->getCar( )->getRoot( ) 
//      && e->getCdr( ) == e->getCdr( )->getRoot( ) )
//      initializeCong( e );
//    // Otherwise specialized initialization
//    // with fake merges
//    else
//      initializeAndMerge( e );
//  }
//
//  assert( initialized.find( top->getId( ) ) != initialized.end( ) );
//}

//void Egraph::initializeAndMerge( Enode * e )
//{
//#if VERBOSE
//  cerr << endl;
//  cerr << "IM: BEGIN INITIALIZING: " << e << endl;
//#endif
//
//  assert( e->getCar( ) != e->getCar( )->getRoot( )
//       || e->getCdr( ) != e->getCdr( )->getRoot( ) );
//  assert( !e->hasCongData( ) );
//  e->allocCongData( );
//  // Node initialized
//  initialized.insert( e->getId( ) );
//
//  // Now we need to adjust data structures as 
//  // either car != car->root or cdr != cdr->root
//
//  Enode * eq = cons( e->getCar( )->getRoot( )
//                   , e->getCdr( )->getRoot( ) );
//
//  // In any case the two terms must be different
//  assert( eq != e );
//  undo_stack_term.push_back( e );
//  undo_stack_oper.push_back( FAKE_MERGE );
//
//#if VERBOSE
//  cerr << "IM: Term: " << e << " is actually equiv to " << eq << endl;
//#endif
//
//  if ( initialized.insert( eq->getId( ) ).second )
//  {
//    assert( !eq->hasCongData( ) );
//    eq->allocCongData( );
//
//    if ( eq->isList( ) )
//      eq->getCar( )->addParent( eq );
//    eq->getCdr( )->addParent( eq );
//
//    undo_stack_term.push_back( eq );
//    undo_stack_oper.push_back( FAKE_INSERT );
//    // Now we need to adjust the signature table
//    // it is possible that the signature of eq is
//    // already used
//    Enode * prev = lookupSigTab( eq );
//    assert( prev != eq );
//    assert( prev == NULL || prev == prev->getCgPtr( ) );
//
//    // Just insert if signature was not there
//    if ( prev == NULL )
//      insertSigTab( eq );
//    // Otherwise prev is the congruence root. This m
//    // eans that eq will not be stored inside sig_tab
//    // However we need to equate the two, as it
//    // is done in normal merge procedure
//    else
//    {
//      // Set congruence pointer to maintain
//      // invariant of signature table
//      eq->setCgPtr( prev );
//      // Add to pending
//      pending.push_back( eq );
//      pending.push_back( prev );
//      // Merge
//      const bool res = mergeLoop( NULL );
//      if ( !res )
//	opensmt_error( "unexpected result" );
//    }
//  }
//#if VERBOSE
//  else
//    cerr << "IM: No need to add: " << eq << endl;
//#endif
//
//#ifdef PEDANTIC_DEBUG
//  assert( !e->isList( ) 
//       || checkParents( e->getCar( ) ) );
//  assert( e->getCdr( )->isEnil( ) 
//       || checkParents( e->getCdr( ) ) );
//#endif
//
//  // Now we need to merge x and eq, since they are equivalent
//  pending.push_back( e );
//  pending.push_back( eq );
//  const bool res = mergeLoop( NULL );
//  if ( !res )
//    opensmt_error( "unexpected result" );
//
//#ifdef PEDANTIC_DEBUG
//  assert( checkParents( e ) );
//  assert( checkParents( eq ) );
//  assert( checkInvariants( ) );
//#endif
//
//#if VERBOSE
//  cerr << "IM: END INITIALING: " << e << endl;
//#endif
//}

//
// Creates a new enode modulo equivalence
//
//Enode * Egraph::uCons( Enode * car, Enode * cdr )
//{
//  assert( false );
//  assert( config.incremental );
//  assert( !config.uf_disable );
//  assert( car );
//  assert( cdr );
//  assert( car->isTerm( ) || car->isSymb( ) || car->isNumb( ) );
//  assert( cdr->isList( ) );
//  // Move to roots
//  car = car->getRoot( );
//  cdr = cdr->getRoot( );
//  Enode * e = NULL;
//  // Create and insert a new enode if necessary
//  e = insertSigTab( id_to_enode.size( ), car, cdr );
//  assert( e );
//  // The node was there already. Return it
//  if ( (enodeid_t)id_to_enode.size( ) != e->getId( ) )
//    return e;
//  assert( e->getCar( ) == e->getCar( )->getRoot( ) );
//  assert( e->getCdr( ) == e->getCdr( )->getRoot( ) );
//  // We keep the created enode
//  id_to_enode.push_back( e );
//  // Initialize its congruence data structures
//  assert( initialized.find( e->getId( ) ) == initialized.end( ) );
//  assert( !e->hasCongData( ) );
//  e->allocCongData( );
//  // Set constant for constants
//  if ( e->isConstant( ) )
//    e->setConstant( e );
//  // Add parents relationships
//  if ( e->isList( ) )
//    e->getCar( )->addParent( e );
//  e->getCdr( )->addParent( e );
//  // Node initialized
//  initialized.insert( e->getId( ) );
//  // Insert in SigTab
//  insertSigTab( e );
//  // Save backtrack info
//  undo_stack_term.push_back( e );
//  undo_stack_oper.push_back( CONS );
//  assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
//  return e;
//}

//void Egraph::undoCons( Enode * e )
//{
//  assert( config.incremental );
//  assert( e );
//  assert( e->isTerm( ) || e->isList( ) );
//  Enode * car = e->getCar( );
//  Enode * cdr = e->getCdr( );
//  assert( car );
//  assert( cdr );
//  // Node must be there
//  assert( lookupSigTab( e ) == e );
//  // Remove from sig_tab
//  removeSigTab( e );
//  // Remove Parent info
//  if ( car->isList( ) )
//    car->removeParent( e );
//  if ( !cdr->isEnil( ) )
//    cdr->removeParent( e );
//  // Remove initialization
//  initialized.erase( e->getId( ) );
//  // Get rid of the correspondence
//  id_to_enode[ e->getId( ) ] = NULL;
//  // Erase the enode
//  delete e;
//}

#ifdef PRODUCE_PROOF
void Egraph::tmpMergeBegin( Enode * x, Enode * y )
{
  assert( config.produce_inter != 0 );
  assert( config.logic == QF_AX
       || config.logic == QF_AXDIFF );

  if ( !x->hasCongData( ) ) x->allocCongData( );
  if ( !y->hasCongData( ) ) y->allocCongData( );

  x = x->getRoot( );
  y = y->getRoot( );

  // x will become root
  // Swap x,y if x is not root
  if ( x->getRoot( ) != x )
  {
    Enode * tmp = x;
    x = y;
    y = tmp;
  }

  // Swap if y is ABcommon and x no
  if ( y->getIPartitions( ) == 6 &&
       x->getIPartitions( ) != 6 )
  {
    Enode * tmp = x;
    x = y;
    y = tmp;
  }

  Enode * v = y;
  const Enode * vstart = v;
  for (;;)
  {
    v->setRoot( x );
    v = v->getNext( );
    if ( v == vstart )
      break;
  }

  // Splice next lists
  Enode * tmp = x->getNext( );
  x->setNext( y->getNext( ) );
  y->setNext( tmp );
  // Update size of the congruence class
  x->setSize( x->getSize( ) + y->getSize( ) );
}

void Egraph::tmpMergeEnd( Enode * x, Enode * y )
{
  assert( config.produce_inter != 0 );
  assert( config.logic == QF_AX
       || config.logic == QF_AXDIFF );

  if ( x->getSize( ) < y->getSize( ) )
  {
    Enode * tmp = x;
    x = y;
    y = tmp;
  }

  // Restore the size of x's class
  x->setSize( x->getSize( ) - y->getSize( ) );
  // Unsplice next lists
  Enode * tmp = x->getNext( );
  x->setNext( y->getNext( ) );
  y->setNext( tmp );
  // Reroot each node of y's eq class back to y
  Enode * v = y;
  const Enode * vstart = v;
  for (;;)
  {
    v->setRoot( y );
    v = v->getNext( );
    if ( v == vstart )
      break;
  }

  assert( x->getRoot( ) != y->getRoot( ) );
}
#endif

//
// Functions to be used when egraph is used 
// as a supporting solver for another theory
// e.g. AX
//
//bool Egraph::extAssertLit( Enode * e )
//{
//  assert( config.uf_disable == 0 );
//  congruence_running = true;
//#ifndef SMTCOMP
//  model_computed = false;
//#endif
//
//  bool res = assertLit_( e );
//
//  return res;
//}

#if MORE_DEDUCTIONS
bool Egraph::deduceMore( vector< Enode * > & saved_deds )
{
  //
  // For each negated equality
  //
  // x != y
  //
  // we see if there are terms
  //
  // rd( a, i )
  // rd( b, j )
  //
  // such that
  //
  // x ~ rd( a, i )
  // y ~ rd( b, j )
  // a ~ b
  //
  // these relations imply that i != j,
  // which is what we (potentially create and)
  // theory-propagate
  //
  bool deduced = false;
  for ( size_t k = 0 ; k < neq_list.size( ) ; k ++ )
  {
    if ( neq_list[ k ]->get1st( )->getRetSort( ) != getSortElem( ) )
      continue;

    vector< Enode * > x_reads, y_reads;

    Enode * x = neq_list[ k ]->get1st( );
    Enode * y = neq_list[ k ]->get2nd( );

    Enode * v = x;
    const Enode * vstart = v;
    for (;;)
    {
      if ( v->isSelect( ) )
	x_reads.push_back( v );

      v = v->getNext( );
      if ( v == vstart )
	break;
    }

    Enode * t = y;
    const Enode * tstart = t;
    for (;;)
    {
      if ( t->isSelect( ) )
	y_reads.push_back( t );

      t = t->getNext( );
      if ( t == tstart )
	break;
    }

    for ( size_t x_i = 0 ; x_i < x_reads.size( ) ; x_i ++ )
    {
      for ( size_t y_i = 0 ; y_i < y_reads.size( ) ; y_i ++ )
      {
	// Check if they are equal in all but one position
	Enode * read1 = x_reads[ x_i ];
	Enode * read2 = y_reads[ y_i ];
	Enode * diff1 = NULL, * diff2 = NULL;

	if ( read1->get1st( )->getRoot( ) ==
	     read2->get1st( )->getRoot( ) )
	{
	  diff1 = x_reads[ x_i ]->get2nd( );
	  diff2 = y_reads[ y_i ]->get2nd( );
	}
	else if ( read1->get2nd( )->getRoot( ) ==
	          read2->get2nd( )->getRoot( ) )
	{
	  Enode * a1 = read1->get1st( );
	  Enode * a2 = read2->get1st( );

	  int nof_diff = 0;

	  while ( nof_diff <= 1 
	      && a1->isStore( ) 
	      && a2->isStore( ) ) 
	  {
	    if ( a1->get3rd( )->getRoot( ) !=
		 a2->get3rd( )->getRoot( ) ) 
	    {
	      // diff1 = a1->get3rd( );
	      // diff2 = a2->get3rd( );
	      // nof_diff ++;
	      // Force exit
	      nof_diff = 2;
	    }
	    if ( a1->get2nd( )->getRoot( ) !=
		 a2->get2nd( )->getRoot( ) ) 
	    {
	      diff1 = a1->get2nd( );
	      diff2 = a2->get2nd( );
	      nof_diff ++;
	    }
	    a1 = a1->get1st( );
	    a2 = a2->get1st( );
	  }

	  // Cannot be different in one
	  if ( !a1->isVar( ) || !a2->isVar( ) )
	    continue;
	  // Different in more than one place
	  if ( nof_diff > 1 )
	    continue;

	  assert( nof_diff == 1 );
	}
	else 
	{
	  continue;
	}

	assert( diff1 );
	assert( diff2 );
	assert( diff1->getRoot( ) != diff2->getRoot( ) );

	Enode * eij = mkEq( cons( diff1
	                  , cons( diff2 ) ) );
	  
	if ( eij->hasPolarity( ) 
	  || eij->isDeduced( ) )
	  continue;

	// Adds if does not exists
	splitOnDemand( eij, id );
	cerr << "DEDUCED: " << eij << endl;
	eij->setDeduced( l_False, id );
	saved_deds.push_back( eij );
	deduced = true;
#ifdef STATISTICS
	tsolvers_stats[ 0 ]->deductions_done ++;
#endif
      }
    }
  }

  return deduced;
}
#endif

//
// Pushes a backtrack point
//
void Egraph::extPushBacktrackPoint( )
{
  // Save solver state if required
  assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
  backtrack_points.push_back( undo_stack_term.size( ) );
}

//
// Pops a backtrack point
//
void Egraph::extPopBacktrackPoint( )
{
  assert( backtrack_points.size( ) > 0 );
  size_t undo_stack_new_size = backtrack_points.back( );
  backtrack_points.pop_back( );
  backtrackToStackSize( undo_stack_new_size );
}
