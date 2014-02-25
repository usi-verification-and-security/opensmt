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

//string Egraph::printEqClass( ERef v )
//{
//    stringstream os;
//    os << "Class of " << v.x << " :" << endl;
//    const ERef vstart = v;
//    for (;;) {
//        os << "   " << v.x << endl;
//        v = enode_store[v].getNext();
//        if ( v == vstart )
//            break;
//    }
//    return os.str();
//}
//

char* Egraph::printEqClass(PTRef tr) const {
    char* out;
    char* old;

    const ERef er = enode_store.termToERef[tr];
    assert(enode_store[er].isTerm());
    ERef c_er = er;
    char* tmp = logic.printTerm(tr);
    asprintf(&out, "In the same eq class with %s are:\n[ ",
             tmp);
    ::free(tmp);

    while (true) {
        const Enode& en = enode_store[c_er];
        ERef next_er = en.getNext();
        if (next_er == er) break;
        const Enode& en_o = enode_store[next_er];
        old = out;
        tmp = logic.printTerm(en_o.getTerm());
        asprintf(&out, "%s%s ", old, tmp);
        ::free(tmp);
        ::free(old);
        c_er = next_er;
    }
    old = out;
    asprintf(&out, "%s]", old);
    ::free(old);
    return out;
}

std::string Egraph::printExplanationTree( PTRef x )
{
    stringstream os;
    while ( x != PTRef_Undef ) {
        os << term_store.printTerm(x);
        if ( expParent.contains(x) && expParent[x] != PTRef_Undef ) {
            os << " --[";
            if ( !expReason.contains(x) )
                os << "<not-contained>";
            else if(expReason[x].tr == PTRef_Undef) {
                os << "<";
                for (int i = 0; i < term_store[x].size(); i++)
                    os << term_store.printTerm(term_store[x][i]) << " ";
                os << ">";
            }
            else
                os << (expReason[x].sgn == l_True ? "" : "not ") << term_store.printTerm(expReason[x].tr);
            if ( expParent.contains(x) && expParent[x] != PTRef_Undef )
                os << "]--> ";
        }
        if (!expParent.contains(x))
            x = PTRef_Undef;
        else
            x = expParent[x];
    }
    return os.str();
}

std::string Egraph::printExplanationTreeDotty( PTRef x )
{
    stringstream os;
    os << "digraph expl" << endl;
    os << "{" << endl;

    while ( x != PTRef_Undef ) {
        os << x.x;
        if ( expParent[x] != PTRef_Undef )
            os << " -> ";
        x = expParent[x];
    }

    os << endl << "}" << endl;
    return os.str();
}


const string Egraph::printDistinctionList( ELRef x, ELAllocator& ela )
{
    if ( x == ELRef_Undef )
        return "";

    std::stringstream os;

    ELRef start = x;
    do {
        os << "+-----------------------------------------------------------+" << endl
           << "| Forbid list node                                          |" << endl
           << "+-----------------------------------------------------------+" << endl
           << "| ELRef: " << x.x << endl
           << "| id: " << ela[x].getId() << endl
           << "| dirty: " << ela[x].isDirty() << endl
           << "| reason: " << (ela[x].reason.sgn == l_True ? "" : "not " ) << logic.printTerm(ela[x].reason.tr) << endl;
        if (ela[x].reloced())
            os << "| reloced to: " << ela[x].rel_e.x << endl;
        else {
            os << "| different from enode " << ela[x].e.x << endl;
            if (enode_store[ela[x].e].isTerm())
                os << "|   term " << logic.printTerm(enode_store[ela[x].e].getTerm()) << endl;
        }
        os << "| link: " << ela[x].link.x << endl;
        os << "+-----------------------------------------------------------+" << endl;

        x = ela[x].link;
    } while( x != start );
    return os.str();
}

void Egraph::checkForbidReferences(ERef er) {
    ELRef start = enode_store[er].getForbid();
    if (start == ELRef_Undef) return;
    ELRef er_old = start;
    do {
        Elist& e_old = forbid_allocator[er_old];
        for (int j = 0; j < forbid_allocator.referenced_by[e_old.getId()].size(); j++) {
            ERef referer = forbid_allocator.referenced_by[e_old.getId()][j];
            assert (e_old.e != referer);
        }

    } while (start != er_old);
}

void Egraph::checkRefConsistency() {
    for (int i = 0; i < forbid_allocator.referenced_by.size(); i++) {
        vec<ERef>& referers = forbid_allocator.referenced_by[i];
        for (int j = 0; j < referers.size(); j++) {
            ERef referer = referers[j];
            if (referer == ERef_Undef) continue;
            ELRef forbid = enode_store[referer].getForbid();
            assert(forbid_allocator[forbid].getId() == i);
        }
    }
}


#ifdef PEDANTIC_DEBUG
const char* Egraph::printUndoTrail() {
    std::stringstream ss;
    for (int i = 0; i < undo_stack_main.size(); i++) {
        Undo& u = undo_stack_main[i];
        oper_t action = u.oper;
        if (action == MERGE) {
            ERef e = u.arg.er;
            Enode& en_e = enode_store[e];
            if (en_e.type() == Enode::et_list)
                ss << i << " --- merge of list" << endl;
            else
                ss << i << " --- merge of terms " << logic.printTerm(en_e.getTerm())
                   << " and " << logic.printTerm(enode_store[u.merged_with].getTerm()) << endl;
        }
        else if (action == DISEQ)
            ss << i << " --- disequality" << endl;
        else
            ss << i << " --- other" << endl;
    }
    // print the equivalence classes of true and false
    return ss.str().c_str();
}
#endif
/*
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
