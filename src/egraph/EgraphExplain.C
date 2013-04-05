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
void Egraph::expStoreExplanation ( ERef x, ERef y, PTRef reason )
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

#ifdef PEDANTIC_DEBUG
    cout << printExpTree( tr_y );
#endif

    if (!expParent.contains(tr_y)) expParent.insert(tr_y, tr_x);
    else expParent[tr_y] = tr_x;

    if (!expReason.contains(tr_y)) expReason.insert(tr_y, reason);
    else expReason[tr_y] = reason;

    // Store both nodes. Because of rerooting operations
    // we don't know whether x --> y or x <-- y at the moment of
    // backtracking. So we just save reason and check both parts
    exp_undo_stack.push(tr_x);
    exp_undo_stack.push(tr_y);

#ifdef PEDANTIC_DEBUG
    assert( checkExpTree(tr_x) );
    assert( checkExpTree(tr_y) );
#endif
}

//
// Subroutine of explainStoreExplanation
// Re-root the tree containing x, in such a way that
// the new root is x itself
//
void Egraph::expReRootOn (PTRef x) {
    PTRef p = x;
    PTRef parent = expParent.contains(p) ? expParent[p] : PTRef_Undef;
    PTRef reason = expReason.contains(p) ? expReason[p] : PTRef_Undef;

    if (!expParent.contains(x))
        expParent.insert(x, PTRef_Undef);
    else
        expParent[x] = PTRef_Undef;

    if (!expReason.contains(x))
        expReason.insert(x, PTRef_Undef);
    else
        expReason[x] = PTRef_Undef;

    while( parent != PTRef_Undef ) {
        // Save grandparent
        PTRef grandparent = expParent.contains(parent) ?  expParent[parent] : PTRef_Undef;

        // Save reason
        PTRef saved_reason = reason;
        reason = expReason.contains(parent) ? expReason[parent] : PTRef_Undef;

        // Reverse edge & reason
        if (expParent.contains(parent)) expParent[parent] = p;
        else expParent.insert(parent, p);

        if (expReason.contains(parent)) expReason[parent] = saved_reason;
        else expReason.insert(parent, saved_reason);

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

        PTRef p = exp_pending.last(); exp_pending.pop();
        PTRef q = exp_pending.last(); exp_pending.pop();

        if ( p == q ) continue;

#ifdef PEDANTIC_DEBUG
        assert( checkExpTree( p ) );
        assert( checkExpTree( q ) );
#endif

        PTRef w = expNCA(p, q);
        assert(w != PTRef_Undef);

        expExplainAlongPath( p, w );
        expExplainAlongPath( q, w );
    }
}

// Exported explain
void Egraph::explain( PTRef x, PTRef y, vec<PTRef> & expl )
{
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

//
// Produce an explanation between nodes x and y
// Wrapper for expExplain
//
void Egraph::expExplain(PTRef x, PTRef y, PTRef
#ifdef PRODUCE_PROOF
    r
#endif
    ) {
    exp_pending.push(x);
    exp_pending.push(y);

#ifdef PRODUCE_PROOF
    if ( config.produce_inter != 0 )
        cgraph.setConf( x, y, r );
#endif

    initDup1();
    expExplain();
    doneDup1();
}

void Egraph::expCleanup() {
  // Destroy the eq classes of the explanation
    while (exp_cleanup.size() != 0) {
        PTRef x = exp_cleanup.last();
        expRoot[x] = x;
        exp_cleanup.pop();
    }
}

//
// Subroutine of explain
// A step of explanation for x and y
//
void Egraph::expExplainAlongPath (PTRef x, PTRef y) {
    PTRef v  = expHighestNode(x);
    PTRef to = expHighestNode(y);

    while ( v != to ) {
        PTRef p = expParent[v];
        assert(p != PTRef_Undef);
        PTRef r = expReason.contains(v) ? expReason[v] : PTRef_Undef;

        // If it is not a congruence edge
        if (r != PTRef_Undef) {
            if ( !isDup1(r) ) {
                explanation.push(r);
                storeDup1(r);
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
        v = expHighestNode( p );
    }
}

void Egraph::expEnqueueArguments(PTRef x, PTRef y) {
    // No explanation needed if they are the same
    if ( x == y )
        return;

    // Simple explanation if they are arity 0 terms
    if ( term_store[x].nargs() == 0 ) {
        exp_pending.push(x);
        exp_pending.push(y);
        return;
    }
    // Otherwise they are the same function symbol
    // Recursively enqueue the explanations for the args
    assert( term_store[x].symb() == term_store[y].symb() );
    for (uint32_t i = 0; i < term_store[x].nargs(); i++) {
        PTRef xptr = term_store[x][i];
        PTRef yptr = term_store[y][i];
        exp_pending.push(xptr);
        exp_pending.push(yptr);
    }
}

void Egraph::expUnion(PTRef x, PTRef y) {
    // Unions are always between a node and its parent
    assert(expParent[x] == y);
    // Retrieve the representant for the explanation class for x and y
    PTRef x_exp_root = expFind(x);
    PTRef y_exp_root = expFind(y);

#ifdef PEDANTIC_DEBUG
    assert(checkExpReachable( x, x_exp_root ) );
    assert(checkExpReachable( y, y_exp_root ) );
#endif

    // No need to merge elements of the same class
    if ( x_exp_root == y_exp_root )
        return;
    // Save highest node. It is always the node of the parent,
    // as it is closest to the root of the explanation tree
    if (!expRoot.contains(x_exp_root))
        expRoot.insert(x_exp_root, y_exp_root);
    else
        expRoot[x_exp_root] = y_exp_root;

    if (!expClassSize.contains(x_exp_root))
        expClassSize.insert(x_exp_root, 0);
    if (!expClassSize.contains(y_exp_root))
        expClassSize.insert(y_exp_root, 0);

    int sz = expClassSize[x_exp_root] + expClassSize[y_exp_root];
    expClassSize[x_exp_root] = sz;
    // Keep track of this union
    exp_cleanup.push(x_exp_root);
    exp_cleanup.push(y_exp_root);

#ifdef PEDANTIC_DEBUG
    assert(checkExpReachable(x, x_exp_root));
    assert(checkExpReachable(y, y_exp_root));
#endif
}

//
// Find the representant of x's equivalence class
// and meanwhile do path compression
// no need for enodes
//
PTRef Egraph::expFind(PTRef x) {
    vec<PTRef> path_compr;
    while (true) {
        // If x is the root, return x
        if ( !expRoot.contains(x) || expRoot[x] == x )
            break;
        path_compr.push(x);
        x = expRoot[x];
    }
    // Path compression
    for (int i = 0; i < path_compr.size(); i++) {
        if (!expRoot.contains(path_compr[i])) expRoot.insert(path_compr[i], x);
        else expRoot[path_compr[i]] = x;
        exp_cleanup.push(path_compr[i]);
    }

    return x;
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
    PTRef h_y = expHighestNode(y);

#ifdef PEDANTIC_DEBUG
    assert(checkExpReachable( x, h_x ));
    assert(checkExpReachable( y, h_y ));
#endif

    while ( h_x != h_y ) {
        if ( h_x != PTRef_Undef ) {
            // We reached a node already marked by h_y
            if ( expTimeStamp.contains(h_x) && expTimeStamp[h_x] == time_stamp )
                return h_x;
            // Mark the node and move to the next
            if (expParent.contains(h_x)) {
                if ( expParent[h_x] != h_x ) {
                    if (!expTimeStamp.contains(h_x))
                        expTimeStamp.insert(h_x, time_stamp);
                    else expTimeStamp[h_x] = time_stamp;
                    h_x = expParent[h_x];
                }
            }
            else h_x = PTRef_Undef; // no parent
        }
        if ( h_y != PTRef_Undef ) {
            // We reached a node already marked by h_x
            if ( expTimeStamp.contains(h_y) && expTimeStamp[h_y] == time_stamp )
                return h_y;
            // Mark the node and move to the next
            if (expParent.contains(h_y)) {
                if ( expParent[h_y] != h_y ) {
                    if (!expTimeStamp.contains(h_y))
                        expTimeStamp.insert(h_y, time_stamp);
                    else
                        expTimeStamp[h_y] = time_stamp;
                    expTimeStamp[h_y] = time_stamp;
                    h_y = expParent[h_y];
                }
            }
            else h_y = PTRef_Undef; // no parent
        }
    }
    // Since h_x == h_y, we return h_x
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
    assert( expParent[x] == y || expParent[y] == x);
    if (expParent[x] == y ) {
        expParent[x] = PTRef_Undef;
        expReason[x] = PTRef_Undef;
    }
    else {
        expParent[y] = PTRef_Undef;
        expReason[y] = PTRef_Undef;
    }
}
