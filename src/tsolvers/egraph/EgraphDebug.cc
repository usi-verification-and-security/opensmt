/*********************************************************************
Author: Antti Hyvarinen <antti.hyarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
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

#include "Egraph.h"

class SimpSMTSolver;

// Choose debugging level
#define CHECK_INVARIANTS                            1
#define CHECK_INVARIANT_FORBID_LIST_SYMMERTRY       0
#define CHECK_INVARIANT_SIGNATURE_TABLE_CORRECTNESS 1

#define CHECK_EXPLANATIONS                          0

#ifdef VERBOSE_EUF

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

char* Egraph::printEqClass(PTRef tr) const {
    char* out;
    char* old;

    const ERef er = enode_store.getERef(tr);
    assert(enode_store[er].isTerm());
    ERef c_er = er;
    char* tmp = logic.printTerm(tr);
    int written = asprintf(&out, "In the same eq class with %s are:\n[ ",
             tmp);
    assert(written >= 0);
    ::free(tmp);

    while (true) {
        const Enode& en = enode_store[c_er];
        ERef next_er = en.getNext();
        if (next_er == er) break;
        const Enode& en_o = enode_store[next_er];
        old = out;
        tmp = logic.printTerm(en_o.getTerm());
        written = asprintf(&out, "%s%s ", old, tmp);
        assert(written >= 0);
        ::free(tmp);
        ::free(old);
        c_er = next_er;
    }
    old = out;
    written = asprintf(&out, "%s]", old);
    assert(written >= 0); (void)written;
    ::free(old);
    return out;
}

std::string Egraph::printExplanationTreeDotty(ERef x)
{
    stringstream os;
    os << "digraph expl" << endl;
    os << "{" << endl;

    while ( x != ERef_Undef ) {
        std::string name = toString(x);
        os << name;
        if (getEnode(x).getExpParent() != ERef_Undef)
            os << " -> ";
        x = getEnode(x).getExpParent();
    }

    os << endl << "}" << endl;
    return os.str();
}

char* Egraph::printDistinctions(PTRef x) const
{
    char* out;
    char* old;

    if (x == PTRef_Undef) {
        assert(false);
        return NULL;
    }

    char* tmp = logic.printTerm(x);
    int written = asprintf(&out, "In different eq class with %s are:\n[ ", tmp);
    assert(written >= 0); (void)written;
    ::free(tmp);


    const ERef er = enode_store[enode_store.getERef(x)].getRoot();
    assert(enode_store[er].isTerm());

    ELRef elr = enode_store[er].getForbid();
    if (elr == ELRef_Undef) {
        char* tmp = out;
        written = asprintf(&out, "%s]", tmp);
        assert(written >= 0);
        free(tmp);
        return out;
    }
    ELRef c_elr = elr;

    while (true) {
        const Elist& el = forbid_allocator[c_elr];
        ELRef next_elr = el.link;
        const Elist& el_o = forbid_allocator[next_elr];
        old = out;
        tmp = logic.printTerm(enode_store[el_o.e].getTerm());
        written = asprintf(&out, "%s%s ", old, tmp);
        assert(written >= 0);
        ::free(tmp);
        ::free(old);
        if (next_elr == elr) break;
        c_elr = next_elr;
    }
    old = out;
    written = asprintf(&out, "%s]", old);
    assert(written >= 0);
    ::free(old);
    return out;
}

const string Egraph::printDistinctionList( ELRef x, ELAllocator& ela, bool detailed )
{
    if ( x == ELRef_Undef )
        return "(undef)";

    std::stringstream os;

    ELRef start = x;
    do {
       if (detailed) {
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
        } else {
            os << "+-----------------------------------------------------------+" << endl
               << "| Forbid list node                                          |" << endl
               << "+-----------------------------------------------------------+" << endl
               << "| reason: " << (ela[x].reason.sgn == l_True ? "" : "not " ) << logic.printTerm(ela[x].reason.tr) << endl;

            os << "| different from enode " << ela[x].e.x << endl;
            if (enode_store[ela[x].e].isTerm())
                os << "|   term " << logic.printTerm(enode_store[ela[x].e].getTerm()) << endl;
        }
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
            assert (e_old.e != forbid_allocator.referenced_by[e_old.getId()][j]);
        }
    } while (start != er_old);
}

void Egraph::checkRefConsistency() {
    for (unsigned int i = 0; i < static_cast<unsigned int>(forbid_allocator.referenced_by.size()); i++) {
        vec<ERef>& referers = forbid_allocator.referenced_by[i];
        for (int j = 0; j < referers.size(); j++) {
            ERef referer = referers[j];
            if (referer == ERef_Undef) continue;
            assert(forbid_allocator[enode_store[referer].getForbid()].getId() == i);
        }
    }
}

std::string Egraph::toString(ERef er) const {
    if (er == ERef_Nil) { return "empty list" ; }
    if (er == ERef_Undef) { return "undef"; }
    const Enode & node = getEnode(er);
    if (node.isSymb()) {
        return logic.printSym(node.getSymb());
    }
    if (node.isTerm()) {
        return logic.printTerm(node.getTerm());
    }
    return "List with head " + toString(node.getCar()) + "\nand tail " + toString(node.getCdr());
}

/*
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
                   << " and " << logic.printTerm(enode_store[u.merged_with].getTerm())
                   << " by term " << logic.printTerm(u.bool_term) << endl;
        }
        else if (action == DISEQ)
            ss << i << " --- disequality by term " << logic.printTerm(u.bool_term) << endl;
        else
            ss << i << " --- other" << endl;
    }
    // print the equivalence classes of true and false
    return ss.str().c_str();
}

const char* Egraph::printAsrtTrail()
{
    std::stringstream ss;
    for (int i = 0; i < undo_stack_main.size(); i++) {
        Undo& u = undo_stack_main[i];
        oper_t action = u.oper;
        if (action == MERGE) {
            ERef e = u.arg.er;
            Enode& en_e = enode_store[e];
            if ((en_e.type() != Enode::et_list) && (en_e.getTerm() != logic.getTerm_false()) && (enode_store[u.merged_with].getTerm() != logic.getTerm_false()))
                ss << i << " --- rel to eq " << logic.printTerm(u.bool_term) << endl;
        }
        else if (action == DISEQ)
            ss << i << " --- rel to diseq " << logic.printTerm(u.bool_term) << endl;
    }
    return ss.str().c_str();
}


#endif
*/
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
