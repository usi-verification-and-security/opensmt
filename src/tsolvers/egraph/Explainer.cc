//
// Created by Martin Blicha on 15.09.20.
//

#include "Explainer.h"

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
void Explainer::expStoreExplanation(ERef x, ERef y, PtAsgn reason)
{
    assert(getEnode(x).isTerm());
    assert(getEnode(y).isTerm());

    // They must be different because the merge hasn't occured yet
    assert(getEnode(x).getRoot() != getEnode(y).getRoot());
    // The main observation here is that the explanation tree, altough
    // differently oriented, has the same size as the equivalence tree
    // (actually we don't keep the equivalence tree, because we use
    // the quick-find approach, but here we just need the size). So we
    // can use root_x.getSize() to know the size of the class of a node
    // x and therefore be sure that the explanation tree is kept
    // balanced (which is a requirement to keep the O(nlogn) bound

    // Make sure that x is the node with the larger number of edges to switch
    const Enode& root_x = getEnode(getEnode(x).getRoot());
    const Enode& root_y = getEnode(getEnode(y).getRoot());
    if ( root_x.getSize() < root_y.getSize() ) {
        ERef tmp = x;
        x = y;
        y = tmp;
    }
    // Reroot the explanation tree on y. It has an amortized cost of logn
    expReRootOn( y );

    getEnode(y).setExpParent(x);
    getEnode(y).setExpReason(reason);
    // Store both nodes. Because of rerooting operations
    // we don't know whether x --> y or x <-- y at the moment of
    // backtracking. So we just save reason and check both parts
    exp_undo_stack.push(x);
    exp_undo_stack.push(y);

#ifdef VERBOSE_EUF
    assert( checkExpTree(getEnode(x).getTerm()) );
    assert( checkExpTree(getEnode(y).getTerm()) );
//    cout << printExplanationTree( tr_y ) << endl;
#endif
}

//
// Subroutine of explainStoreExplanation
// Re-root the tree containing x, in such a way that
// the new root is x itself
//
void Explainer::expReRootOn(ERef x) {
    ERef p = x;
    ERef parent = getEnode(p).getExpParent();
    PtAsgn reason = getEnode(p).getExpReason();
    getEnode(x).setExpParent(ERef_Undef);
    getEnode(x).setExpReason(PtAsgn_Undef);
    while( parent != ERef_Undef ) {
        // Save grandparent
        ERef grandparent = getEnode(parent).getExpParent();
        // Save reason
        PtAsgn saved_reason = reason;
        reason = getEnode(parent).getExpReason();
        // Reverse edge & reason
        getEnode(parent).setExpParent(p);
        getEnode(parent).setExpReason(saved_reason);

#ifdef VERBOSE_EUF
        assert( checkExpTree( getEnode(parent).getTerm() ) );
#endif

        // Move the two pointers
        p = parent;
        parent = grandparent;
    }
}

void Explainer::expExplain() {
    initDup();
    while ( exp_pending.size() > 0 ) {
        assert( exp_pending.size() % 2 == 0 );

        ERef p = exp_pending.last(); exp_pending.pop();
        ERef q = exp_pending.last(); exp_pending.pop();

        if ( p == q ) continue;

#ifdef VERBOSE_EUF
        assert( checkExpTree( getEnode(p).getTerm() ) );
        assert( checkExpTree( getEnode(q).getTerm() ) );
#endif
#ifdef VERBOSE_EUFEX
        cerr << "Explain " << toString(p) << " and " << toString(q) << endl;
#endif
        ERef w = expNCA(p, q);
        assert(w != ERef_Undef);

#ifdef VERBOSE_EUFEX
        cerr << "Explaining along path " << toString(p) << " -> " << toString(w) << endl;
#endif
        expExplainAlongPath( p, w );
#ifdef VERBOSE_EUFEX
        cerr << "Explaining along path " << toString(q) << " -> " << toString(w) << endl;
#endif
        expExplainAlongPath( q, w );
    }
    doneDup();
    expCleanup();
}

//
// Produce an explanation between nodes x and y
// Wrapper for expExplain
//
void Explainer::expExplain(ERef x, ERef y)
{
#ifdef VERBOSE_EUFEX
    cerr << "exp pending size " << exp_pending.size() << endl;
    cerr << "explain pushing " << toString(x) << " and " << toString(y) << endl;
#endif
    exp_pending.push(x);
    exp_pending.push(y);
    expExplain();
}

void Explainer::expCleanup() {
    // Destroy the eq classes of the explanation
    // May be reversed once debug's fine
#ifdef VERBOSE_EUFEX
    cerr << "Cleanup called" << endl;
#endif
    for (int i = exp_cleanup.size()-1; i >= 0; i--) {
        auto x = exp_cleanup[i];
        getEnode(x).setExpRoot(x);
#ifdef VERBOSE_EUFEX
        cerr << "clean: " << toString(x) << endl;
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
void Explainer::expExplainAlongPath(ERef x, ERef y) {
    auto v  = expHighestNode(x);
    // Why this? Not in the pseudo code!
    auto to = expHighestNode(y);

#ifdef VERBOSE_EUFEX
    cerr << "Explaining " << toString(v) << " to " << toString(to) << endl;
#endif
    while ( v != to ) {
        ERef p = getEnode(v).getExpParent();
        assert(p != ERef_Undef);
        expExplainEdge(v,p);
        ERef v_old = v;
        v = expHighestNode( p );
        if (v_old == v)
            assert(false); // loop in the explanation graph!
    }
}

void Explainer::expEnqueueArguments(ERef x, ERef y) {
    // No explanation needed if they are the same
    if (x == y) {
        return;
    }
    assert(getEnode(x).isTerm() && getEnode(y).isTerm());
    // They have the same function symbol
    // Recursively enqueue the explanations for the args
    // Use the canonical representative here in case the UF solver
    // detected an equivalence!
    assert( getEnode(x).getCar() == getEnode(y).getCar() );
    assert(getEnode(getEnode(x).getCar()).isSymb());
    ERef cdr_x = getEnode(x).getCdr();
    ERef cdr_y = getEnode(y).getCdr();
    ERef ERef_Nil = store.get_Nil();
    while(cdr_x != ERef_Nil) {
        assert(cdr_y != ERef_Nil);
        assert(getEnode(cdr_x).isList());
        assert(getEnode(cdr_y).isList());
        ERef xptr = getEnode(cdr_x).getCar();
        ERef yptr = getEnode(cdr_y).getCar();
        assert(getEnode(xptr).isTerm());
        assert(getEnode(yptr).isTerm());
#ifdef VERBOSE_EUFEX
        cerr << "in loop pushing " << toString(xptr) << " and " << toString(yptr) << endl;
#endif
        exp_pending.push(xptr);
        exp_pending.push(yptr);
        cdr_x = getEnode(cdr_x).getCdr();
        cdr_y = getEnode(cdr_y).getCdr();
    }
    assert(cdr_y == ERef_Nil);
}

void Explainer::expExplainEdge(const ERef v, const ERef p) {
    assert(getEnode(v).getExpParent() == p);
    PtAsgn r = getEnode(v).getExpReason();

    // If it is not a congruence edge
    if (r.tr != PTRef_Undef) {
//        AH: It seems that bringing the required propositional vars to the egraph reintroduces the duplicates
//        assert(!isDup(r.tr)); // MB: It seems that with the shortcuts stored in expRoot, duplicates will never be encountered
        if (not isDup(r.tr)) {
            explanation.push(r);
            storeDup(r.tr);
        }
    }
        // Otherwise it is a congruence edge
        // This means that the edge is linking nodes
        // like (v)f(a1,...,an) (p)f(b1,...,bn), and that
        // a1,...,an = b1,...bn. For each pair ai,bi
        // we have therefore to compute the reasons
    else {
        assert(getEnode(v).getCar() == getEnode(p).getCar());
        expEnqueueArguments(v, p);
    }
    expUnion(v, p);
}

void Explainer::expUnion(ERef x, ERef y) {
#ifdef VERBOSE_EUFEX
    cerr << "Union: " << toString(x) << " " << toString(y) << endl;
#endif
    // Unions are always between a node and its parent
    assert(getEnode(x).getExpParent() == y);
    // Retrieve the representant for the explanation class for x and y
    ERef x_exp_root = expFind(x);
    ERef y_exp_root = expFind(y);
#ifdef VERBOSE_EUFEX
    cerr << "Root of " << toString(x) << " is " << toString(x_exp_root) << endl;
    cerr << "Root of " << toString(y) << " is " << toString(y_exp_root) << endl;
#endif

#ifdef VERBOSE_EUF
    assert(checkExpReachable( getEnode(x).getTerm(), getEnode(x_exp_root).getTerm() ) );
    assert(checkExpReachable( getEnode(y).getTerm(), getEnode(y_exp_root).getTerm() ) );
#endif

    // No need to merge elements of the same class
    if ( x_exp_root == y_exp_root )
        return;
    // Save highest node. It is always the node of the parent,
    // as it is closest to the root of the explanation tree
    getEnode(x_exp_root).setExpRoot(y_exp_root);

    // Keep track of this union
#ifdef VERBOSE_EUFEX
    cerr << "Union: cleanup " << toString(x_exp_root) << endl;
#endif
    exp_cleanup.push(x_exp_root);
#ifdef VERBOSE_EUFEX
    cerr << "Union: cleanup " << toString(y_exp_root) << endl;
#endif
    exp_cleanup.push(y_exp_root);

#ifdef VERBOSE_EUF
    assert(checkExpReachable(getEnode(x).getTerm(), getEnode(x_exp_root).getTerm()));
    assert(checkExpReachable(getEnode(y).getTerm(), getEnode(y_exp_root).getTerm()));
#endif
}

//
// Find the representant of x's equivalence class
// and meanwhile do path compression
//
ERef Explainer::expFind(ERef x) {
    // If x is the root, return x
    if (getEnode(x).getExpRoot() == x) return x;
    // Recurse
#ifdef VERBOSE_EUFEX
    cerr << "expFind: " << toString(x) << endl;
#endif
    ERef exp_root = expFind(getEnode(x).getExpRoot());
    // Path compression
    if (exp_root != getEnode(x).getExpRoot()) {
        getEnode(x).setExpRoot(exp_root);
#ifdef VERBOSE_EUFEX
        cerr << "expFind: cleanup " << toString(x) << endl;
#endif
        exp_cleanup.push(x);
    }
    return exp_root;
}

ERef Explainer::expHighestNode(ERef x) {
    ERef x_exp_root = expFind(x);
    return x_exp_root;
}

//
// Explain Nearest Common Ancestor
//

ERef Explainer::expNCA(ERef x, ERef y) {
    // Increase time stamp
    ++time_stamp;

    auto h_x = expHighestNode(x);
#ifdef VERBOSE_EUFEX
    cerr << "Highest node of " << toString(x) << " is " << toString(h_x) << endl;
#endif
    auto h_y = expHighestNode(y);
#ifdef VERBOSE_EUFEX
    cerr << "Highest node of " << toString(y) << " is " << toString(h_y) << endl;
#endif
#ifdef VERBOSE_EUF
    assert(checkExpReachable( getEnode(x).getTerm(), getEnode(h_x).getTerm()));
    assert(checkExpReachable( getEnode(y).getTerm(), getEnode(h_y).getTerm() ));
#endif

    while ( h_x != h_y ) {
        assert(h_x == ERef_Undef || getEnode(h_x).getExpTimeStamp() <= time_stamp);
        assert(h_y == ERef_Undef || getEnode(h_y).getExpTimeStamp() <= time_stamp);
        if ( h_x != ERef_Undef ) {
            // We reached a node already marked by h_y
            if (getEnode(h_x).getExpTimeStamp() == time_stamp) {
#ifdef VERBOSE_EUFEX
                cerr << "found x, " << toString(h_x) << endl;
#endif
                return h_x;
            }

            // Mark the node and move to the next
#ifdef VERBOSE_EUFEX
            // MB: this does not work any, there is no term_store member anymore
//            cerr << "x: ExpParent of " << logic.printTerm(h_x) << " is "
//                 << (term_store[h_x].getExpParent() == PTRef_Undef ? "undef" : logic.printTerm(term_store[h_x].getExpParent())) << endl;
#endif
            if (getEnode(h_x).getExpParent() != h_x) {
                getEnode(h_x).setExpTimeStamp(time_stamp);
                h_x = getEnode(h_x).getExpParent();
            }
        }
        if ( h_y != ERef_Undef ) {
            // We reached a node already marked by h_x
            if (getEnode(h_y).getExpTimeStamp() == time_stamp) {
#ifdef VERBOSE_EUFEX
                cerr << "found y, " << toString(h_y) << endl;
#endif
                return h_y;
            }
            // Mark the node and move to the next
            if (getEnode(h_y).getExpParent() != h_y) {
                getEnode(h_y).setExpTimeStamp(time_stamp);
                h_y = getEnode(h_y).getExpParent();
            }
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
void Explainer::expRemoveExplanation() {
    assert(exp_undo_stack.size() >= 2);

    auto x = exp_undo_stack.last();
    exp_undo_stack.pop();
    auto y = exp_undo_stack.last();
    exp_undo_stack.pop();

    assert( x != ERef_Undef );
    assert( y != ERef_Undef );

    // We observe that we don't need to undo the rerooting
    // of the explanation trees, because it doesn't affect
    // correctness. We just have to reroot y on itself
    assert( getEnode(x).getExpParent() == y || getEnode(y).getExpParent() == x);
    if (getEnode(x).getExpParent() == y ) {
        getEnode(x).setExpParent(ERef_Undef);
        getEnode(x).setExpReason(PtAsgn_Undef);
    }
    else {
        getEnode(y).setExpParent(ERef_Undef);
        getEnode(y).setExpReason(PtAsgn_Undef);
    }
}

void Explainer::fillExplanation(vec<PtAsgn> & expl) {
    for (auto entry : explanation) {
        expl.push(entry);
    }
    explanation.clear();
}
