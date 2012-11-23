/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
      , Edgar Pek           <edgar.pek@lu.unisi.ch>
      , Aliaksei Tsitovich  <aliaksei.tsitovich@usi.ch>

OpenSMT -- Copyright (C) 2008-2010, Roberto Bruttomesso

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

#include "DLSolver.h"
#include "DLGraph.h"
// Included to compile templates
#include "DLGraph.C"

#define DLVERBOSE 0

//
// Allocates a new graph
//
template< class T > void DLSolver<T>::initGraph( )
{
  G = new DLGraph<T>( config, egraph );
}
//
// Deallocate graph
//
template< class T > DLSolver<T>::~DLSolver( )
{
  delete G;
}
//
// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is
// called before the actual solving starts.
//
template< class T > lbool DLSolver<T>::inform( Enode * e )
{
  assert( e );
  assert( belongsToT( e ) );
  assert( !e->hasPolarity( ) );
  assert( e->isLeq( ) );
#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0 
       || e->getIPartitions( ) != 0 );
#endif
  G->insertStatic( e );
  return l_Undef;
}

//
// Asserts a literal into the solver. If by chance
// you are able to discover inconsistency you may
// return false. The real consistency state will
// be checked with "check"
//
template< class T > bool DLSolver<T>::assertLit ( Enode * e, bool reason )
{
  assert( e );
  assert( belongsToT( e ) );
  assert( e->hasPolarity( ) );
  //
  // If we are doing eager computation / lazy communication
  //
  DLEdge<T> * deduced_edge = G->getOppositePolarityEdge( e );
  if ( reason && G->isGreedy( )  )
  {
    // Find the shortest path p for the deduced edge
    DLPath & shortest_path = G->getShortestPath( deduced_edge );
    assert( ! shortest_path.empty( ) );
    explanation.push_back( e );
    for ( typename DLPath::iterator it = shortest_path.begin( ); it != shortest_path.end( ); ++ it )
        explanation.push_back( (*it)->c );
    return false;
  }

  if ( e->isDeduced( )
    && e->getDeduced( ) == e->getPolarity( )
    && e->getDedIndex( ) == id )
    return true;

  undo_stack_edges.push_back( e );
  //G->insertDynamic          ( e );
  const bool res = G->checkNegCycle( e, reason );
  //const bool res = G->checkNegCycleDFS( e, reason );

  // Return true if satisfiable
  if ( res )
  {
    assert( false == reason );
    if ( config.dl_theory_propagation > 0 )
    {
      G->findHeavyEdges( e );
      sendDeductions( );
    }
    return true;
  }
  //
  // Otherwise retrieve and store negative cycle
  //
  DLVertex<T> * s = G->getNegCycleVertex( );
  DLVertex<T> * u = s;
  DLPath & conflictEdges = G->getConflictEdges( );
  DLPath lazy_spath;
  do
  {
    DLEdge<T> *edge = conflictEdges[u->id];
    u = edge->u;
    explanation.push_back( edge->c );
    if ( reason )
      lazy_spath.push_back( edge );
  }
  while(s != u);

  return false;
}

template< class T > void DLSolver<T>::pushBacktrackPoint ( )
{
  //
  // Undo_stack_deduced_edges is used in the lazy_eager schema
  //
  if ( G->isGreedy( ) )
  {
    backtrack_points.push_back( G->undo_stack_deduced_edges.size( ) );
  }
  //
  // Backtrack_points.push_back( G->undo_stack_inactive_enodes.size( ) );
  //
  backtrack_points.push_back( undo_stack_edges.size( ) );
}

template< class T >void DLSolver<T>::popBacktrackPoint ( )
{
  assert( G->heavy_edges.empty( ) );
  assert( backtrack_points.size( ) > 0 );
  //
  // Backtrack to dyn edges stack size
  //
  size_t undo_stack_new_size = backtrack_points.back( );
  backtrack_points.pop_back( );
  backtrackToDynEdgesStackSize( undo_stack_new_size );

  if ( G->isGreedy( ) )
  {
    undo_stack_new_size = backtrack_points.back( );
    backtrack_points.pop_back( );
    backtrackToDeducedEdgesStackSize( undo_stack_new_size );
  }

}

template < class T> bool DLSolver<T>::check( bool complete )
{
  (void)complete;
  //
  // Here check for consistency
  //
  return true;
}

//
// DL Atoms have one of these shapes
//
// (<= (+ (* 1 x) (* (~ 1) y)) c)
// (<= (+ (* (~ 1) x) (* 1 y)) c)
// (<= (* (~ 1) x) c)
// (<= (* 1 x) c)
//
template< class T > bool DLSolver<T>::belongsToT( Enode * e )
{
  assert( e );

  if ( !e->isLeq( ) )
    return false;

  Enode * lhs = e->get1st( );
  Enode * rhs = e->get2nd( );

  if ( !lhs->isConstant( ) && !rhs->isConstant( ) )
    return false;

  if ( lhs->isConstant( ) )
  {
    Enode * tmp = lhs;
    lhs = rhs;
    rhs = tmp;
  }

  Real one_ = 1;
  Real mone_ = -1;
  Enode * one = egraph.mkNum( one_ );
  Enode * mone = egraph.mkNum( mone_ );
  //
  // Two variables
  //
  if ( lhs->isPlus( ) )
  {
    if ( lhs->getArity( ) != 2 ) return false;
    Enode * mon_1 = lhs->get1st( );
    Enode * mon_2 = lhs->get2nd( );
    if ( !mon_1->isTimes( ) ) return false;
    if ( !mon_2->isTimes( ) ) return false;
    Enode * const_1 = mon_1->get1st( );
    Enode * const_2 = mon_2->get1st( );
    Enode * var_1 = mon_1->get2nd( );
    Enode * var_2 = mon_2->get2nd( );
    if ( config.logic == QF_UFIDL && config.sat_lazy_dtc != 0 )
    {
      if ( !var_1->isVar( ) && !var_1->isUf( ) ) return false;
      if ( !var_2->isVar( ) && !var_2->isUf( ) ) return false;
    }
    else
    {
      if ( !var_1->isVar( ) || !var_2->isVar( ) ) return false;
    }
    if ( !const_1->isConstant( ) || !const_2->isConstant( ) ) return false;
    if ( const_1 == one && const_2 == mone ) return true;
    if ( const_2 == one && const_1 == mone ) return true;
    return false;
  }
  //
  // One variable
  //

  if ( lhs->getArity( ) < 2 )
  {
    opensmt_error2( "Malformed term: ", e );
  }

  Enode * con = lhs->get1st( );
  Enode * var = lhs->get2nd( );
  if ( con != one && con != mone ) return false;
  if ( config.logic == QF_UFIDL && config.sat_lazy_dtc != 0 )
  {
    if ( !var->isVar( ) && !var->isUf( ) ) return false;
  }
  else
  {
    if ( !var->isVar( ) ) return false;
  }

  return true;
}

// Backtrack stack to the size
template< class T>void DLSolver<T>::backtrackToDynEdgesStackSize( size_t size )
{
  // Restore the state at the previous backtrack point
  while ( undo_stack_edges.size( ) > size )
  {
    Enode * e = undo_stack_edges.back( );
    undo_stack_edges.pop_back( );
    G->deleteActive( e );
  }
}

//
// FIXME: make sure it is correctly handled
//
template< class T>void DLSolver<T>::backtrackToInactiveEnodesStackSize( size_t size )
{
  // Restore the state at the previous backtrack point
  while ( G->undo_stack_inactive_enodes.size( ) > size )
  {
    Enode * e = G->undo_stack_inactive_enodes.back( );
    G->undo_stack_inactive_enodes.pop_back( );
    G->insertInactive( e );
  }

}

template< class T >void DLSolver<T>::backtrackToDeducedEdgesStackSize( size_t size )
{
  while ( G->undo_stack_deduced_edges.size( ) > size )
  {
    DLEdge<T> * e = G->undo_stack_deduced_edges.back( );
    G->undo_stack_deduced_edges.pop_back( );
    G->clearShortestPath( e );
  }
}

template< class T >void DLSolver<T>::sendDeductions ( )
{
  while ( ! (G->heavy_edges).empty() )
  {
    DLEdge<T> *edge = (G->heavy_edges).back( );
    (G->heavy_edges).pop_back( );
    assert( ! edge->c->hasPolarity( ) );
    assert ( ! edge->c->isDeduced  ( ) );
    //
    // By construction: positive edges have even id (hence, negative edges have odd id)
    //
    edge->c->setDeduced( ( edge->id % 2 ) ? l_False : l_True, id );
    deductions.push_back( edge->c );
  }
}

template< class T >void DLSolver<T>::computeModel( )
{
  G->computeModel( );
}

#ifdef PRODUCE_PROOF
//
// Compute interpolants for the conflict
//
template<class T> Enode * DLSolver<T>::getInterpolants( logic_t & l )
{
  l = config.logic == QF_IDL || config.logic == QF_UFIDL
    ? QF_IDL
    : QF_RDL ;

  DLVertex< T > * s = G->getNegCycleVertex( );
  DLVertex< T > * u = s;
  DLPath & conflictEdges = G->getConflictEdges( );

  assert( conflictEdges.size( ) > 1 );

  list< Enode * > in_list;
  // Set the mask as 1..10
  ipartitions_t mask = 1;
  mask = ~mask;
  // Scan the various partitions
  for( unsigned in = 1 ; in < egraph.getNofPartitions( ) ; in ++ )
  {
    // Keeps track of A-chords, to be conjoined at the end
    list< Enode * > conj;
    // mask &= ~SETBIT( in );
    clrbit( mask, in );
    // Compute intermediate interpolants

    bool A_path = false;
    bool B_seen = false;
    bool AB_mixed = false;

    Enode * i_begin = NULL;
    Enode * i_end   = NULL;

    T chord_summary = 0;

    // iterate over conflict - negative cycle
    do
    {
      DLEdge< T > * edge = conflictEdges[ u->id ];
      const ipartitions_t & p = edge->c->getIPartitions( );
      icolor_t color = I_UNDEF;

      if ( isABmixed( p ) )
      {
	assert( config.logic == QF_UFLRA
	     || config.logic == QF_UFIDL );
	AB_mixed = true;
	break;
      }

      if ( isAB( p, mask ) )
	color = I_AB;
      else if ( isAlocal( p, mask ) )
	color = I_A;
      else if ( isBlocal( p, mask ) )
	color = I_B;

      assert( color == I_A 
	   || color == I_AB 
	   || color == I_B );

      assert( config.proof_set_inter_algo == 0
	   || config.proof_set_inter_algo == 1
	   || config.proof_set_inter_algo == 2 );

      // McMillan algo: set AB as B
      if ( config.proof_set_inter_algo == 0
	&& color == I_AB )
	color = I_B;
      // McMillan' algo: set AB as a
      else if ( config.proof_set_inter_algo == 2
	     && color == I_AB )
	color = I_A;
      // Pudlak algo: who cares
      else if ( config.proof_set_inter_algo == 1
	     && color == I_AB )
	color = I_A;

      assert( color == I_A 
	   || color == I_B );

      // Update begin of the chord while itarating through A edges
      if( color == I_A )
      {
        // If A path is already going just accumulate constant
        if( A_path )
        {
	  // Update last vertex
          i_end = edge->u->e;
          chord_summary += edge->wt;
        }
        // Otherwise start the A path
        else
        {
          A_path = true;
          i_begin = edge->v->e;
          i_end   = edge->u->e;
          chord_summary = edge->wt;
        }
      }
      // Once B edge is discovered there are 3 options:
      else
      {
	// B has been seen -- interpolant is not trivially false
	B_seen = true;

	// If an A-path was in progress, create chord
        if( A_path )
        {
	  if ( i_begin && i_end )
	    conj.push_back( egraph.mkLeq( egraph.cons( egraph.mkMinus( egraph.cons( i_end
								     , egraph.cons( i_begin ) ) )
					, egraph.cons( egraph.mkNum( chord_summary ) ) ) ) );
	  else if ( i_begin )
	    conj.push_back( egraph.mkLeq( egraph.cons( egraph.mkUminus( egraph.cons( i_begin ) ) 
					, egraph.cons( egraph.mkNum( chord_summary ) ) ) ) );
	  else if ( i_end )
	    conj.push_back( egraph.mkLeq( egraph.cons( i_end
		                        , egraph.cons( egraph.mkNum( chord_summary ) ) ) ) );
	  else
	    conj.push_back( egraph.mkFalse( ) );
	}

	// No A-path in progress
	A_path = false;
      }
      // Move to the next edge
      u = edge->u;
    }
    while( s != u );
    
    // If an A-path was in progress, create chord
    if( A_path )
    {
      if ( i_begin && i_end )
	conj.push_back( egraph.mkLeq( egraph.cons( egraph.mkMinus( egraph.cons( i_end
								 , egraph.cons( i_begin ) ) )
				    , egraph.cons( egraph.mkNum( chord_summary ) ) ) ) );
      else if ( i_begin )
	conj.push_back( egraph.mkLeq( egraph.cons( egraph.mkUminus( egraph.cons( i_begin ) )
				    , egraph.cons( egraph.mkNum( chord_summary ) ) ) ) );
      else if ( i_end )
	conj.push_back( egraph.mkLeq( egraph.cons( i_end 
				    , egraph.cons( egraph.mkNum( chord_summary ) ) ) ) );
      else
	conj.push_back( egraph.mkFalse( ) );
    }

    // Conflict is all in A, interpolant is false
    if ( AB_mixed )
      in_list.push_front( egraph.mkFakeInterp( ) );
    else if ( !B_seen )
      in_list.push_front( egraph.mkFalse( ) );
    else
      in_list.push_front( egraph.mkAnd( egraph.cons( conj ) ) );
  }
  interpolants = egraph.cons( in_list );
  return interpolants;
}

#endif
