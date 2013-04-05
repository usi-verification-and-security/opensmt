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

class SimpSMTSolver;

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

bool Egraph::checkExp () {
#if CHECK_EXPLANATIONS
    assert( explanation.size() > 1 );
    // Check for duplicated literals in conflict
    set< enodeid_t > visited;
    for ( unsigned i = 0 ; i < explanation.size( ) ; i ++ ) {
        if ( visited.find( term_store[explanation[i]].getId() ) != visited.end( ) ) {
            cerr << "Error: explanation " << explanation[i] << " is present twice" << endl;
            return false;
        }
        visited.insert( term_store[explanation[i]].getId() );
    }

    return true;
#else
    return true;
#endif
}


bool Egraph::checkExpTree ( PTRef x ) {
    assert( x != PTRef_Undef );
#if CHECK_EXPLANATIONS
     set< PTRef > visited;

    while ( expParent.contains(x) ) {
        if ( expReason.contains(x) ) {
            if ( visited.find( expReason[x] ) != visited.end() ) {
                cerr << "Error: explanation is present twice" << endl;
                return false;
            }
        }
        visited.insert( expReason[x] );
        x = expReason[x];
    }

    return true;
#else
    return true;
#endif
}

bool Egraph::checkExpReachable( PTRef x, PTRef h_x ) {
    assert( x != PTRef_Undef );
    assert( h_x != PTRef_Undef );
#if CHECK_EXPLANATIONS
    PTRef orig = x;

    if ( x == h_x )
        return true;

    while ( expParent[x] != h_x ) {
        x = expParent[x];
        if ( x == PTRef_Undef ) {
            cerr << h_x << " is unreachable from " << orig << endl;
            return false;
        }
    }

    return true;
#else
    return true;
#endif
}

#endif

//=============================================================================
// Printing Routines

string Egraph::printEqClass( ERef v )
{
    stringstream os;
    os << "Class of " << v.x << " :" << endl;
    const ERef vstart = v;
    for (;;) {
        os << "   " << v.x << endl;
    v = enode_store[v].getNext();
    if ( v == vstart )
        break;
    }
    return os.str();
}

std::string Egraph::printExplanation() {
    stringstream os;
    os << "# Conflict: ";
    for ( int i = 0 ; i < explanation.size( ) ; i ++ ) {
        if ( i > 0 )
            os << ", ";

//        assert( explanation[ i ]->hasPolarity( ) );
        assert(solver->value(tmap.termToVar[explanation[i]]) != l_Undef);
        if ( solver->value(tmap.termToVar[explanation[i]]) == l_False )
            os << "!";

        os << explanation[i].x;
    }
    os << endl;
    return os.str();
}

std::string Egraph::printExplanationTree( ERef x )
{
    stringstream os;
    while ( x != ERef_Undef ) {
        os << x.x;
        if ( expParent[x] != ERef_Undef )
            os << " --[";
        if ( expReason[x] != ERef_Undef )
            os << expReason[x].x;
        if ( expParent[x]->getExpParent( ) != ERef_Undef )
            os << "]--> ";
        x = expParent[x];
    }
    return os.str();
}

std::string Egraph::printExplanationTreeDotty( ERef x )
{
    stringstream os;
    os << "digraph expl" << endl;
    os << "{" << endl;

    while ( x != ERef_Undef ) {
        os << x.x;
        if ( expParent[x] != ERef_Undef )
            os << " -> ";
        x = expParent[x];
    }

    os << endl << "}" << endl;
    return os.str();
}
/*
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
