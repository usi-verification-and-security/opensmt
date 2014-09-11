/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

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

//=============================================================================
// Explanation Routines: details about these routines are in paper
//
// Robert Nieuwenhuis and Albert Oliveras
// "Proof Producing Congruence Closure"
// @inproceedings{DBLP:conf/rta/NieuwenhuisO05,
//  author    = {Robert Nieuwenhuis and
//               Albert Oliveras},
//  title     = {Proof-Producing Congruence Closure},
//  booktitle = {Term Rewriting and Applications, 16th International Conference,
//                RTA 2005, Nara, Japan, April 19-21, 2005, Proceedings},
//  year      = {2005},
//  pages     = {453-468},
//  editor    = {J{\"u}rgen Giesl},
//  publisher = {Springer},
//  series    = {Lecture Notes in Computer Science},
//  volume    = {3467},
//  year      = {2005},
// }

//
// Store explanation for an eq merge
//
void Egraph::expStoreExplanation ( ERef x, ERef y, PtAsgn reason )
{
    assert(enode_store[x].isTerm());
    assert(enode_store[y].isTerm());

    // They must be different because the merge hasn't occured yet
    assert( enode_store[x].getRoot() != enode_store[y].getRoot() );
    // The main observation here is that the explanation tree, altough
    // differently oriented, has the same size as the equivalence tree
    // (actually we don't keep the equivalence tree, because we use
    // the quick-find approach, but here we just need the size). So we
    // can use root_x.getSize() to know the size of the class of a node
    // x and therefore be sure that the explanation tree is kept
    // balanced (which is a requirement to keep the O(nlogn) bound

    // Make sure that x is the node with the larger number of edges to switch
    Enode& root_x = enode_store[enode_store[x].getRoot()];
    Enode& root_y = enode_store[enode_store[y].getRoot()];
    if ( root_x.getSize() < root_y.getSize() ) {
        ERef tmp = x;
        x = y;
        y = tmp;
    }

    PTRef tr_y = enode_store[y].getTerm();
    PTRef tr_x = enode_store[x].getTerm();

    // Reroot the explanation tree on y. It has an amortized cost of logn
    expReRootOn( tr_y );

#ifdef TERMS_HAVE_EXPLANATIONS
    term_store[tr_y].setExpParent(tr_x);
    term_store[tr_y].setExpReason(reason);
#else
    term_store.setParent(tr_y, tr_x);
    term_store.setReason(tr_y, reason);
#endif
    // Store both nodes. Because of rerooting operations
    // we don't know whether x --> y or x <-- y at the moment of
    // backtracking. So we just save reason and check both parts
    exp_undo_stack.push(tr_x);
    exp_undo_stack.push(tr_y);

#ifdef PEDANTIC_DEBUG
    assert( checkExpTree(tr_x) );
    assert( checkExpTree(tr_y) );
//    cout << printExplanationTree( tr_y ) << endl;
#endif
}

//
// Subroutine of explainStoreExplanation
// Re-root the tree containing x, in such a way that
// the new root is x itself
//
void Egraph::expReRootOn (PTRef x) {
    PTRef p = x;
#ifdef TERMS_HAVE_EXPLANATIONS
    PTRef parent = term_store[p].getExpParent();
    PtAsgn reason = term_store[p].getExpReason();
    term_store[x].setExpParent(PTRef_Undef);
    term_store[x].setExpReason(PtAsgn_Undef);
#else
    PTRef parent = term_store.getParent(p);
    PtAsgn reason = term_store.getReason(p);
    term_store.setParent(x, PTRef_Undef);
    term_store.setReason(x, PtAsgn_Undef);
#endif
    while( parent != PTRef_Undef ) {
        // Save grandparent
#ifdef TERMS_HAVE_EXPLANATIONS
        PTRef grandparent = term_store[parent].getExpParent();
#else
        PTRef grandparent = term_store.getParent(parent);
#endif
        // Save reason
        PtAsgn saved_reason = reason;
#ifdef TERMS_HAVE_EXPLANATIONS
        reason = term_store[parent].getExpReason();
        // Reverse edge & reason
        term_store[parent].setExpParent(p);
        term_store[parent].setExpReason(saved_reason);
#else
        reason = term_store.getReason(parent);
        // Reverse edge & reason
        term_store.setParent(parent, p);
        term_store.setReason(parent, saved_reason);
#endif

#ifdef PEDANTIC_DEBUG
        assert( checkExpTree( parent ) );
#endif

        // Move the two pointers
        p = parent;
        parent = grandparent;
    }
}

void Egraph::expExplain () {
    while ( exp_pending.size() > 0 ) {
        assert( exp_pending.size() % 2 == 0 );

        PTRef p_in = exp_pending.last(); exp_pending.pop();
        PTRef q_in = exp_pending.last(); exp_pending.pop();

        ERef p_er = enode_store.termToERef[p_in];
        PTRef p = enode_store.ERefToTerm[p_er];
        ERef q_er = enode_store.termToERef[q_in];
        PTRef q = enode_store.ERefToTerm[q_er];

        if ( p == q ) continue;

#ifdef PEDANTIC_DEBUG
        assert( checkExpTree( p ) );
        assert( checkExpTree( q ) );
#endif
#ifdef VERBOSE_EUFEX
        cerr << "Explain " << logic.printTerm(p) << " and " << logic.printTerm(q) << endl;
#endif
        PTRef w = expNCA(p, q);
        assert(w != PTRef_Undef);

#ifdef VERBOSE_EUFEX
//        cerr << "Explanation from " << term_store.printTerm(p) << " to " << term_store.printTerm(w) << ":" << endl;
//        cerr << " " << printExplanationTree(p) << endl;
//        cerr << "Explanation from " << term_store.printTerm(q) << " to " << term_store.printTerm(w) << ":" << endl;
//        cerr << " " <<printExplanationTree(q) << endl;
#endif
#ifdef VERBOSE_EUFEX
        cerr << "Explaining along path " << logic.printTerm(p) << " -> " << logic.printTerm(w) << endl;
#endif
        expExplainAlongPath( p, w );
#ifdef VERBOSE_EUFEX
        cerr << "Explaining along path " << logic.printTerm(q) << " -> " << logic.printTerm(w) << endl;
#endif
        expExplainAlongPath( q, w );
    }
}

// Exported explain
/*
void Egraph::explain( PTRef x, PTRef y, vec<PTRef> & expl )
{
    assert(false);
    assert(explanation.size() == 0);
    if (x == y) return;
    expExplain(x, y, PTRef_Undef);
    assert(explanation.size() > 0);
    for (int i = 0; i < explanation.size(); i++)
        expl.push(explanation[i]);
    expCleanup( );
    explanation.clear( );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter != 0 )
        cgraph.clear( );
#endif
}
*/
//
// Produce an explanation between nodes x and y
// Wrapper for expExplain
//
#ifndef PRODUCE_PROOF
void Egraph::expExplain(PTRef x, PTRef y)
#else
void Egraph::expExplain(PTRef x, PTRef y, PTRef r)
#endif
{
#ifdef VERBOSE_EUFEX
    cerr << "exp pending size " << exp_pending.size() << endl;
    cerr << "explain pushing " << logic.printTerm(x) << " and " << logic.printTerm(y) << endl;
#endif
    exp_pending.push(x);
    exp_pending.push(y);

#ifdef PRODUCE_PROOF
    if ( config.produce_inter != 0 )
        cgraph.setConf( x, y, r );
#endif

    initDup1();
    expExplain();
    doneDup1();
    expCleanup();
}

void Egraph::expCleanup() {
    // Destroy the eq classes of the explanation
    // May be reversed once debug's fine
#ifdef VERBOSE_EUFEX
    cerr << "Cleanup called" << endl;
#endif
    for (int i = exp_cleanup.size()-1; i >= 0; i--) {
        PTRef x = exp_cleanup[i];
#ifdef TERMS_HAVE_EXPLANATIONS
        term_store[x].setExpRoot(x);
#else
        term_store.setRoot(x, x);
#endif
#ifdef VERBOSE_EUFEX
        cerr << "clean: " << logic.printTerm(x) << endl;
#endif
// These are not used
//        assert(expHighestNode.contains(x));
//        expHighestNode[x] = x;
    }
    exp_cleanup.clear();
}

//
// Subroutine of explain
// A step of explanation for x and y
//
void Egraph::expExplainAlongPath (PTRef x, PTRef y) {
    PTRef v  = expHighestNode(x);
    // Why this? Not in the pseudo code!
    PTRef to = expHighestNode(y);
#ifdef VERBOSE_EUFEX
    cerr << "Explaining " << logic.printTerm(v) << " to " << logic.printTerm(to) << endl;
#endif
    while ( v != to ) {
#ifdef TERMS_HAVE_EXPLANATIONS
        PTRef p = term_store[v].getExpParent();
#else
        PTRef p = term_store.getParent(v);
#endif
        if (p == PTRef_Undef)
            cerr << "weirdness " << logic.printTerm(v) << endl;
        assert(p != PTRef_Undef);
#ifdef TERMS_HAVE_EXPLANATIONS
        PtAsgn r = term_store[v].getExpReason();
#else
        PtAsgn r = term_store.getReason(v);
#endif

        // If it is not a congruence edge
        if (r.tr != PTRef_Undef && r.tr != Eq_FALSE) {
            if ( !isDup1(r.tr) ) {
                explanation.push(r);
                storeDup1(r.tr);
            }
        }
        // Otherwise it is a congruence edge
        // This means that the edge is linking nodes
        // like (v)f(a1,...,an) (p)f(b1,...,bn), and that
        // a1,...,an = b1,...bn. For each pair ai,bi
        // we have therefore to compute the reasons
        else {
            assert( term_store[v].symb() == term_store[p].symb() );
            assert( term_store[v].nargs() == term_store[p].nargs() );
            expEnqueueArguments( v, p );
        }

#ifdef PRODUCE_PROOF
        if ( config.produce_inter != 0 ) {
            cgraph.addCNode( v );
            cgraph.addCNode( p );
            cgraph.addCEdge( v, p, r );
        }
#endif

        expUnion( v, p );
        PTRef v_old = v;
        v = expHighestNode( p );
        if (v_old == v)
            assert(false); // loop in the explanation graph!
    }
}

void Egraph::expEnqueueArguments(PTRef x, PTRef y) {
    // No explanation needed if they are the same
    if ( x == y )
        return;

    // Simple explanation if they are arity 0 terms
    if ( term_store[x].nargs() == 0 ) {
#ifdef VERBOSE_EUFEX
        cerr << "pushing " << logic.printTerm(x) << " and " << logic.printTerm(y) << endl;
#endif
        exp_pending.push(x);
        exp_pending.push(y);
        return;
    }
    // Otherwise they are the same function symbol
    // Recursively enqueue the explanations for the args
    // Use the canonical representative here in case the UF solver
    // detected an equivalence!
    assert( term_store[x].symb() == term_store[y].symb() );
    for (uint32_t i = 0; i < term_store[x].nargs(); i++) {
        PTRef xptr = term_store[x][i];
        PTRef yptr = term_store[y][i];
#ifdef VERBOSE_EUFEX
        cerr << "in loop pushing " << logic.printTerm(xptr) << " and " << logic.printTerm(yptr) << endl;
#endif
        exp_pending.push(xptr);
        exp_pending.push(yptr);
    }
}

void Egraph::expUnion(PTRef x, PTRef y) {
#ifdef VERBOSE_EUFEX
    cerr << "Union: " << logic.printTerm(x) << " " << logic.printTerm(y) << endl;
#endif
    // Unions are always between a node and its parent
#ifdef TERMS_HAVE_EXPLANATIONS
    assert(term_store[x].getExpParent() == y);
#else
    assert(term_store.getParent(x) == y);
#endif
    // Retrieve the representant for the explanation class for x and y
    PTRef x_exp_root = expFind(x);
    PTRef y_exp_root = expFind(y);
#ifdef VERBOSE_EUFEX
    cerr << "Root of " << logic.printTerm(x) << " is " << logic.printTerm(x_exp_root) << endl;
    cerr << "Root of " << logic.printTerm(y) << " is " << logic.printTerm(y_exp_root) << endl;
#endif

#ifdef PEDANTIC_DEBUG
    assert(checkExpReachable( x, x_exp_root ) );
    assert(checkExpReachable( y, y_exp_root ) );
#endif

    // No need to merge elements of the same class
    if ( x_exp_root == y_exp_root )
        return;
    // Save highest node. It is always the node of the parent,
    // as it is closest to the root of the explanation tree
#ifdef TERMS_HAVE_EXPLANATIONS
    term_store[x_exp_root].setExpRoot(y_exp_root);
#else
    term_store.setRoot(x_exp_root, y_exp_root);
#endif

    // Keep track of this union
#ifdef VERBOSE_EUFEX
    cerr << "Union: cleanup " << logic.printTerm(x_exp_root) << endl;
#endif
    exp_cleanup.push(x_exp_root);
#ifdef VERBOSE_EUFEX
    cerr << "Union: cleanup " << logic.printTerm(y_exp_root) << endl;
#endif
    exp_cleanup.push(y_exp_root);

#ifdef PEDANTIC_DEBUG
    assert(checkExpReachable(x, x_exp_root));
    assert(checkExpReachable(y, y_exp_root));
#endif
}

//
// Find the representant of x's equivalence class
// and meanwhile do path compression
//
PTRef Egraph::expFind(PTRef x) {
    // If x is the root, return x
#ifdef TERMS_HAVE_EXPLANATIONS
    if (term_store[x].getExpRoot() == x) return x;
#else
    if (term_store.getRoot(x) == x) return x;
#endif
    // Recurse
#ifdef VERBOSE_EUFEX
    cerr << "expFind: " << logic.printTerm(x) << endl;
#endif
#ifdef TERMS_HAVE_EXPLANATIONS
    PTRef exp_root = expFind(term_store[x].getExpRoot());
#else
    PTRef exp_root = expFind(term_store.getRoot(x));
#endif
    // Path compression
#ifdef TERMS_HAVE_EXPLANATIONS
    if (exp_root != term_store[x].getExpRoot()) {
        term_store[x].setExpRoot(exp_root);
#else
    if (exp_root != term_store.getRoot(x)) {
        term_store.setRoot(x, exp_root);
#endif
#ifdef VERBOSE_EUFEX
        cerr << "expFind: cleanup " << logic.printTerm(x) << endl;
#endif
        exp_cleanup.push(x);
    }
    return exp_root;
}

PTRef Egraph::expHighestNode(PTRef x) {
    PTRef x_exp_root = expFind(x);
    return x_exp_root;
}

//
// Explain Nearest Common Ancestor
//

PTRef Egraph::expNCA(PTRef x, PTRef y) {
    // Increase time stamp
    time_stamp ++;

    PTRef h_x = expHighestNode(x);
#ifdef VERBOSE_EUFEX
    cerr << "Highest node of " << logic.printTerm(x) << " is " << logic.printTerm(h_x) << endl;
#endif
    PTRef h_y = expHighestNode(y);
#ifdef VERBOSE_EUFEX
    cerr << "Highest node of " << logic.printTerm(y) << " is " << logic.printTerm(h_y) << endl;
#endif
#ifdef PEDANTIC_DEBUG
    assert(checkExpReachable( x, h_x ));
    assert(checkExpReachable( y, h_y ));
#endif

    while ( h_x != h_y ) {
        if ( h_x != PTRef_Undef ) {
            // We reached a node already marked by h_y
#ifdef TERMS_HAVE_EXPLANATIONS
            if (term_store[h_x].getExpTimeStamp() == time_stamp) {
#else
            if (term_store.getTimeStamp(h_x) == time_stamp) {
#endif
#ifdef VERBOSE_EUFEX
                cerr << "found x, " << logic.printTerm(h_x) << endl;
#endif
                return h_x;
            }

            // Mark the node and move to the next
#ifdef VERBOSE_EUFEX
#ifdef TERMS_HAVE_EXPLANATIONS
            cerr << "x: ExpParent of " << logic.printTerm(h_x) << " is " << (term_store[h_x].getExpParent() == PTRef_Undef ? "undef" : logic.printTerm(term_store[h_x].getExpParent())) << endl;
#else
            cerr << "x: ExpParent of " << logic.printTerm(h_x) << " is " << (term_store.getParent(h_x) == PTRef_Undef ? "undef" : logic.printTerm(term_store.getParent(h_x))) << endl;
#endif
#endif
#ifdef TERMS_HAVE_EXPLANATIONS
            if (term_store[h_x].getExpParent() != h_x) {
                term_store[h_x].setExpTimeStamp(time_stamp);
                h_x = term_store[h_x].getExpParent();
            }
#else
            if (term_store.getParent(h_x) != h_x) {
                term_store.setTimeStamp(h_x, time_stamp);
                h_x = term_store.getParent(h_x);
            }
#endif
        }
        if ( h_y != PTRef_Undef ) {
            // We reached a node already marked by h_x
#ifdef TERMS_HAVE_EXPLANATIONS
            if (term_store[h_y].getExpTimeStamp() == time_stamp) {
#else
            if (term_store.getTimeStamp(h_y) == time_stamp) {
#endif
#ifdef VERBOSE_EUFEX
                cerr << "found y, " << logic.printTerm(h_y) << endl;
#endif
                return h_y;
            }
            // Mark the node and move to the next
#ifdef VERBOSE_EUFEX
#ifdef TERMS_HAVE_EXPLANATIONS
            cerr << "y: ExpParent of " << logic.printTerm(h_y) << " is " << (term_store[h_y].getExpParent() == PTRef_Undef ? "undef" : logic.printTerm(term_store[h_y].getExpParent())) << endl;
#else
            cerr << "y: ExpParent of " << logic.printTerm(h_y) << " is " << (term_store.getParent(h_y) == PTRef_Undef ? "undef" : logic.printTerm(term_store.getParent(h_y))) << endl;
#endif
#endif
#ifdef TERMS_HAVE_EXPLANATIONS
            if (term_store[h_y].getExpParent() != h_y) {
                term_store[h_y].setExpTimeStamp(time_stamp);
                h_y = term_store[h_y].getExpParent();
            }
#else
            if (term_store.getParent(h_y) != h_y) {
                term_store.setTimeStamp(h_y, time_stamp);
                h_y = term_store.getParent(h_y);
            }
#endif
        }
    }
    // Since h_x == h_y, we return h_x
    assert(h_x == h_y);
    return h_x;
}

//
// Undoes the effect of expStoreExplanation
// No need for enodes
//
void Egraph::expRemoveExplanation() {
    assert(exp_undo_stack.size() >= 2);

    PTRef x = exp_undo_stack.last();
    exp_undo_stack.pop();
    PTRef y = exp_undo_stack.last();
    exp_undo_stack.pop();

    assert( x != PTRef_Undef );
    assert( y != PTRef_Undef );

    // We observe that we don't need to undo the rerooting
    // of the explanation trees, because it doesn't affect
    // correctness. We just have to reroot y on itself
#ifdef TERMS_HAVE_EXPLANATIONS
    assert( term_store[x].getExpParent() == y || term_store[y].getExpParent() == x);
    if (term_store[x].getExpParent() == y ) {
        term_store[x].setExpParent(PTRef_Undef);
        term_store[x].setExpReason(PtAsgn_Undef);
    }
    else {
        term_store[y].setExpParent(PTRef_Undef);
        term_store[y].setExpReason(PtAsgn_Undef);
    }
#else
    assert(term_store.getParent(x) == y || term_store.getParent(y) == x);
    if (term_store.getParent(x) == y) {
        term_store.setParent(x, PTRef_Undef);
        term_store.setReason(x, PtAsgn_Undef);
    }
    else {
        term_store.setParent(y, PTRef_Undef);
        term_store.setReason(y, PtAsgn_Undef);
    }
#endif
}
