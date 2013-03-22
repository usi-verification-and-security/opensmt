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

#include "Egraph.h"
#include "SigTab.h"

// Choose debugging level
#define CHECK_INVARIANTS                            1
#define CHECK_INVARIANT_FORBID_LIST_SYMMERTRY       0
#define CHECK_INVARIANT_SIGNATURE_TABLE_CORRECTNESS 1

#define CHECK_EXPLANATIONS                          0

#ifdef PEDANTIC_DEBUG

bool Egraph::checkInvariants( )
{
#if CHECK_INVARIANTS
  // Check forbid list symmetry
  // TODO: TBD
#if CHECK_INVARIANT_FORBID_LIST_SYMMERTRY
  if ( !checkInvariantFLS( ) )
    return false;
#endif
  // Check signature table correctness
#if CHECK_INVARIANT_SIGNATURE_TABLE_CORRECTNESS
  if ( !checkInvariantSTC( ) )
    return false;
#endif
#endif
  return true;
}



bool Egraph::checkParents( ERef e )
{
    if (e == ERef_Nil) return true;
    assert( enode_store[e].isList( ) || enode_store[e].isTerm( ) );
    Enode& en_e = enode_store[e];
    const bool scdr = en_e.isList( );
    ERef p = en_e.getParent( );

    const ERef pstart = p;
    int count = 0;
    for ( ; p != ERef_Undef ; ) {
        assert ( enode_store[p].isTerm( ) || enode_store[p].isList( ) );
        if ( scdr && enode_store[enode_store[p].getCdr()].getRoot( ) != en_e.getRoot( ) ) {
            cerr << "Parent invariant broken in parents of " << e.x << ": "
                 << enode_store[enode_store[p].getCdr()].getRoot().x
                 << " differs from"
                 << en_e.getRoot().x
                 << endl;
            assert(false);
            return false;
        }
        if ( !scdr && enode_store[enode_store[p].getCar( )].getRoot( ) != en_e.getRoot( ) ) {
            cerr << "Parent invariant broken in parents of " << e.x << ": "
                 << enode_store[enode_store[p].getCar()].getRoot( ).x
                 << " differs from "
                 << en_e.getRoot( ).x
                 << endl;
            assert(false);
            return false;
        }
        // Next element
        p = scdr ? enode_store[p].getSameCdr( ) : enode_store[p].getSameCar( ) ;
        // End of cycle
        if ( p == pstart )
            p = ERef_Undef;
        count ++;
    }
    if ( en_e.getParent( ) == ERef_Undef && en_e.getParentSize( ) != 0 ) {
        cerr << "Parent invariant broken: " 
             << endl
             << " wrong parent size for " 
             << e.x
             << endl;
        assert(false);
        return false;
    }
    // This invariant is valid only if it has some parents 
    // (see "Merge parent lists": if y is empty
    // it will stay empty, as y will not become
    // root ...)
    if ( count != enode_store[en_e.getRoot()].getParentSize( ) && en_e.getParent( ) != ERef_Undef ) {
        cerr << "Parent invariant broken: "
             << endl
             << " wrong parent size for "
             << e.x << " (" << en_e.getRoot( ).x << ")"
             << "(" << enode_store.printEnode(e) << ")"
             << "; "
             << endl
             << " they should be "
             << enode_store[en_e.getRoot( )].getParentSize( )
             << " but they are "
             << count
             << endl;
        assert(false);
        return false;
    }

    return true;
}

/*
bool Egraph::checkExp ( )
{
#if CHECK_EXPLANATIONS
  assert( explanation.size( ) > 1 );
  // Check for duplicated literals in conflict
  set< enodeid_t > visited;
  for ( unsigned i = 0 ; i < explanation.size( ) ; i ++ )
  {
    if ( visited.find( explanation[ i ]->getId( ) ) != visited.end( ) )
    {
      cerr << "Error: explanation " << explanation[ i ] << " is present twice" << endl;
      return false;
    }
    visited.insert( explanation[ i ]->getId( ) );
  }

  return true;
#else
  return true;
#endif
}

bool Egraph::checkExpTree ( Enode * x )
{
  assert( x );
#if CHECK_EXPLANATIONS
  set< Reason * > visited;

  while ( x->getExpParent( ) != NULL )
  {
    if ( x->getExpReason( ) != NULL )
    {
      if ( visited.find( x->getExpReason( ) ) != visited.end( ) )
      {
	cerr << "Error: explanation is present twice" << endl;
	return false;
      }
      visited.insert( x->getExpReason( ) );
    }
    x = x->getExpParent( );
  }

  return true;
#else
  return true;
#endif
}

bool Egraph::checkExpReachable( Enode * x, Enode * h_x )
{
  assert( x );
  assert( h_x );
#if CHECK_EXPLANATIONS
  Enode * orig = x;

  if ( x == h_x )
    return true;

  while ( x->getExpParent( ) != h_x )
  {
    x = x->getExpParent( );
    if ( x == NULL )
    {
      cerr << h_x << " is unreachable from " << orig << endl;
      return false;
    }
  }

  return true;
#else
  return true;
#endif
}
*/
#endif
/*
//=============================================================================
// Printing Routines

void Egraph::printEqClass( ostream & os, Enode * v )
{
  os << "Class of " << v << " :" << endl;
  const Enode * vstart = v;
  for (;;)
  {
    os << "   " << v << endl;
    v = v->getNext( );
    if ( v == vstart )
      break;
  }
}

void Egraph::printExplanation( ostream & os )
{
  os << "# Conflict: ";
  for ( unsigned i = 0 ; i < explanation.size( ) ; i ++ )
  {
    if ( i > 0 )
      os << ", ";

    assert( explanation[ i ]->hasPolarity( ) );
    if ( explanation[ i ]->getPolarity( ) == l_False )
      os << "!";

    explanation[ i ]->print( os );
  }
  os << endl;
}

void Egraph::printExplanationTree( ostream & os, Enode * x )
{
  while ( x != NULL )
  {
    os << x;
    if ( x->getExpParent( ) != NULL )
      os << " --[";
    if ( x->getExpReason( ) != NULL )
      os << x->getExpReason( );
    if ( x->getExpParent( ) != NULL )
      os << "]--> ";
    x = x->getExpParent( );
  }
}

void Egraph::printExplanationTreeDotty( ostream & os, Enode * x )
{
  os << "digraph expl" << endl;
  os << "{" << endl;

  while ( x != NULL )
  {
    os << x;
    if ( x->getExpParent( ) != NULL )
      os << " -> ";
    x = x->getExpParent( );
  }

  os << endl << "}" << endl;
}

void Egraph::printDistinctionList( ostream & os, Enode * x )
{
  Elist * l = x->getForbid( );

  if ( l == NULL )
    return;

  string sep = "";
  do
  {
    os << sep;
    sep = ", ";
    l->e->print( os );
    l = l->link;
  }
  while( l != x->getForbid( ) );
}

void Egraph::printParents( ostream & os, Enode * w )
{
  assert( w->hasCongData( ) );
  Enode * p = w->getParent( );
  const Enode * pstart = p;
  // w might be NULL, i.e. it may not have fathers
  const bool scdr = w == NULL ? false : w->isList( );
  if ( p != NULL ) os << "Parents of " << w << " :" << endl;
  else os << "No parents for " << w << endl;
  for ( ; p != NULL ; )
  {
    assert( p->isTerm( ) || p->isList( ) );
    os << "  " << p << endl;
    // Next element
    p = scdr ? p->getSameCdr( ) : p->getSameCar( ) ;
    // End of cycle
    if ( p == pstart )
      p = NULL;
  }
}
*/
