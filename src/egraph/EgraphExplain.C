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

//=============================================================================
// Explanation Routines: details about these routines are in paper
//
// Robert Nieuwenhuis and Albert Oliveras
// "Proof Producing Congruence Closure"

//
// Store explanation for an eq merge
//
void Egraph::expStoreExplanation ( Enode * x, Enode * y, Enode * reason )
{
  assert( x->isTerm( ) );
  assert( y->isTerm( ) );
  // They must be different because the merge hasn't occured yet
  assert( x->getRoot( ) != y->getRoot( ) );
  // The main observation here is that the explanation tree, altough
  // differently oriented, has the same size as the equivalence tree
  // (actually we don't keep the equivalence tree, because we use
  // the quick-find approach, but here we just need the size). So we
  // can use x->getRoot( )->getSize( ) to know the size of the class of a node
  // x and therefore be sure that the explanation tree is kept
  // balanced (which is a requirement to keep the O(nlogn) bound

  // Make sure that x is the node with the larger number of edges to switch
  if ( x->getRoot( )->getSize( ) < y->getRoot( )->getSize( ) )
  {
    Enode * tmp = x;
    x = y;
    y = tmp;
  }

  // Reroot the explanation tree on y. It has an amortized cost of logn
  expReRootOn( y );
  y->setExpParent( x );
  y->setExpReason( reason );

  // Store both nodes. Because of rerooting operations
  // we don't know whether x --> y or x <-- y at the moment of
  // backtracking. So we just save reason and check both parts
  exp_undo_stack.push_back( x );
  exp_undo_stack.push_back( y );

#ifdef PEDANTIC_DEBUG
  assert( checkExpTree( x ) );
  assert( checkExpTree( y ) );
#endif
}

//
// Subroutine of explainStoreExplanation
// Re-root the tree containing x, in such a way that
// the new root is x itself
//
void Egraph::expReRootOn ( Enode * x )
{
  Enode * p = x;
  Enode * parent = p->getExpParent( );
  Enode * reason = p->getExpReason( );
  x->setExpParent( NULL );
  x->setExpReason( NULL );

  while( parent != NULL )
  {
    // Save grandparent
    Enode * grandparent = parent->getExpParent( );

    // Save reason
    Enode * saved_reason = reason;
    reason = parent->getExpReason( );

    // Reverse edge & reason
    parent->setExpParent( p );
    parent->setExpReason( saved_reason );

#ifdef PEDANTIC_DEBUG
    assert( checkExpTree( parent ) );
#endif

    // Move the two pointers
    p = parent;
    parent = grandparent;
  }
}

void Egraph::expExplain ( )
{
  while ( !exp_pending.empty( ) )
  {
    assert( exp_pending.size( ) % 2 == 0 );

    Enode * p = exp_pending.back( ); exp_pending.pop_back( );
    Enode * q = exp_pending.back( ); exp_pending.pop_back( );

    if ( p == q ) continue;

#ifdef PEDANTIC_DEBUG
    assert( checkExpTree( p ) );
    assert( checkExpTree( q ) );
#endif

    Enode * w = expNCA( p, q );
    assert( w );

    expExplainAlongPath( p, w );
    expExplainAlongPath( q, w );
  }
}

// Exported explain
void Egraph::explain( Enode * x, Enode * y, vector< Enode * > & expl )
{
  assert( explanation.empty( ) );
  if ( x == y ) return;
  expExplain( x, y, NULL );
  assert( !explanation.empty( ) );
  expl.insert( expl.end( ), explanation.begin( ), explanation.end( ) );
  expCleanup( );
  explanation.clear( );
#ifdef PRODUCE_PROOF
  if ( config.produce_inter != 0 )
    cgraph.clear( );
#endif
}

//
// Produce an explanation between nodes x and y
// Wrapper for expExplain
//
void Egraph::expExplain ( Enode * x, Enode * y, Enode * 
#ifdef PRODUCE_PROOF
    r 
#endif
    )
{
  exp_pending.push_back( x );
  exp_pending.push_back( y );

#ifdef PRODUCE_PROOF
  if ( config.produce_inter != 0 )
    cgraph.setConf( x, y, r );
#endif

  initDup1( );
  expExplain( );
  doneDup1( );
}

void Egraph::expCleanup ( )
{
  // Destroy the eq classes of the explanation
  while ( !exp_cleanup.empty( ) )
  {
    Enode * x = exp_cleanup.back( );
    x->setExpRoot( x );
    x->setExpHighestNode( x );
    exp_cleanup.pop_back( );
  }
}

//
// Subroutine of explain
// A step of explanation for x and y
//
void Egraph::expExplainAlongPath ( Enode * x, Enode * y )
{
  Enode * v  = expHighestNode( x );
  Enode * to = expHighestNode( y );

  while ( v != to )
  {
    Enode * p = v->getExpParent( );
    assert( p != NULL );
    Enode * r = v->getExpReason( );

    // If it is not a congruence edge
    if ( r != NULL )
    {
      if ( !isDup1( r ) )
      {
	assert( r->isTerm( ) );
	explanation.push_back( r );
	storeDup1( r );
      }
    }
    // Otherwise it is a congruence edge
    // This means that the edge is linking nodes
    // like (v)f(a1,...,an) (p)f(b1,...,bn), and that
    // a1,...,an = b1,...bn. For each pair ai,bi
    // we have therefore to compute the reasons
    else
    {
      assert( v->getCar( ) == p->getCar( ) );
      assert( v->getArity( ) == p->getArity( ) );
      expEnqueueArguments( v, p );
    }

#ifdef PRODUCE_PROOF
    if ( config.produce_inter != 0 )
    {
      cgraph.addCNode( v );
      cgraph.addCNode( p );
      cgraph.addCEdge( v, p, r );
    }
#endif

    expUnion( v, p );
    v = expHighestNode( p );
  }
}

void Egraph::expEnqueueArguments( Enode * x, Enode * y )
{
  assert( x->isTerm( ) );
  assert( y->isTerm( ) );
  assert( x->getArity( ) == y->getArity( ) );
  // No explanation needed if they are the same
  if ( x == y )
    return;

  // Simple explanation if they are arity 0 terms
  if ( x->getArity( ) == 0 )
  {
    exp_pending.push_back( x );
    exp_pending.push_back( y );
    return;
  }
  // Otherwise they are the same function symbol
  // Recursively enqueue the explanations for the args
  assert( x->getCar( ) == y->getCar( ) );
  Enode * xptr = x->getCdr( );
  Enode * yptr = y->getCdr( );
  while ( !xptr->isEnil( ) )
  {
    exp_pending.push_back( xptr->getCar( ) );
    exp_pending.push_back( yptr->getCar( ) );
    xptr = xptr->getCdr( );
    yptr = yptr->getCdr( );
  }
  // Check both lists have the same length
  assert( yptr->isEnil( ) );
}

void Egraph::expUnion ( Enode * x, Enode * y )
{
  // Unions are always between a node and its parent
  assert( x->getExpParent( ) == y );
  // Retrieve the representant for the explanation class for x and y
  Enode * x_exp_root = expFind( x );
  Enode * y_exp_root = expFind( y );

#ifdef PEDANTIC_DEBUG
  assert( checkExpReachable( x, x_exp_root ) );
  assert( checkExpReachable( y, y_exp_root ) );
#endif

  // No need to merge elements of the same class
  if ( x_exp_root == y_exp_root )
    return;
  // Save highest node. It is always the node of the parent,
  // as it is closest to the root of the explanation tree
  x_exp_root->setExpRoot( y_exp_root );
  x_exp_root->setExpClassSize( x_exp_root->getExpClassSize( ) + y_exp_root->getExpClassSize( ) );
  // Keep track of this union
  exp_cleanup.push_back( x_exp_root );
  exp_cleanup.push_back( y_exp_root );

#ifdef PEDANTIC_DEBUG
  assert( checkExpReachable( x, x_exp_root ) );
  assert( checkExpReachable( y, y_exp_root ) );
#endif
}

//
// Find the representant of x's equivalence class
// and meanwhile do path compression
//
Enode * Egraph::expFind ( Enode * x )
{
  // If x is the root, return x
  if ( x->getExpRoot( ) == x )
    return x;

  // Recursively find the representant
  Enode * exp_root = expFind( x->getExpRoot( ) );
  // Path compression
  if ( exp_root != x->getExpRoot( ) )
  {
    x->setExpRoot( exp_root );
    exp_cleanup.push_back( x );
  }

  return exp_root;
}

Enode * Egraph::expHighestNode ( Enode * x )
{
  Enode * x_exp_root = expFind( x );
  return x_exp_root;
}

Enode * Egraph::expNCA ( Enode * x, Enode * y )
{
  // Increase time stamp
  time_stamp ++;

  Enode * h_x = expHighestNode( x );
  Enode * h_y = expHighestNode( y );

#ifdef PEDANTIC_DEBUG
  assert( checkExpReachable( x, h_x ) );
  assert( checkExpReachable( y, h_y ) );
#endif

  while ( h_x != h_y )
  {
    if ( h_x != NULL )
    {
      // We reached a node already marked by h_y
      if ( h_x->getExpTimeStamp( ) == time_stamp )
	return h_x;
      // Mark the node and move to the next
      if ( h_x->getExpParent( ) != h_x )
      {
	h_x->setExpTimeStamp( time_stamp );
	h_x = h_x->getExpParent( );
      }
    }
    if ( h_y != NULL )
    {
      // We reached a node already marked by h_x
      if ( h_y->getExpTimeStamp( ) == time_stamp )
	return h_y;
      // Mark the node and move to the next
      if ( h_y->getExpParent( ) != h_y )
      {
	h_y->setExpTimeStamp( time_stamp );
	h_y = h_y->getExpParent( );
      }
    }
  }
  // Since h_x == h_y, we return h_x
  return h_x;
}

//
// Undoes the effect of expStoreExplanation
//
void Egraph::expRemoveExplanation( )
{
  assert( exp_undo_stack.size( ) >= 2 );

  Enode * x = exp_undo_stack.back( );
  exp_undo_stack.pop_back( );
  Enode * y = exp_undo_stack.back( );
  exp_undo_stack.pop_back( );

  assert( x );
  assert( y );
  assert( !x->isEnil( ) );
  assert( !y->isEnil( ) );

  // We observe that we don't need to undo the rerooting
  // of the explanation trees, because it doesn't affect
  // correctness. We just have to reroot y on itself
  assert( x->getExpParent( ) == y || y->getExpParent( ) == x );
  if ( x->getExpParent( ) == y )
  {
    x->setExpParent( NULL );
    x->setExpReason( NULL );
  }
  else
  {
    y->setExpParent( NULL );
    y->setExpReason( NULL );
  }
}
