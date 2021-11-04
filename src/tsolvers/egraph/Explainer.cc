//
// Created by Martin Blicha on 15.09.20.
//

#include "Explainer.h"
#include "UFInterpolator.h"
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

/**
 * Store explanation for an eq merge.
 * @arg x a term
 * @arg y a term to be set to the class of x
 * @Preconditions: x & y are terms and not in the same equivalence class.
 * @Postcondition: let u, v be the node in {x, y} with the smaller, respectively larger, equivalence graph. The graph of u will be re-rooted on v.
*/
void Explainer::storeExplanation(ERef x, ERef y, PtAsgn reason)
{
    assert(getEnode(x).getRoot() != getEnode(y).getRoot());

    // They must be different because the merge hasn't occured yet
    if (getEnode(x).getRoot() == getEnode(y).getRoot()) {
        throw OsmtInternalException("Attempting to store explanation for already known equality");
    }
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
        swap(x,y);
    }
    // Reroot the explanation tree on y. It has an amortized cost of logn
    reRootOn( y );

    getEnode(y).setExpParent(x);
    getEnode(y).setExpReason(reason);
    // Store both nodes. Because of rerooting operations
    // we don't know whether x --> y or x <-- y at the moment of
    // backtracking. So we just save reason and check both parts
    exp_undo_stack.push(x);
    exp_undo_stack.push(y);
}

//
// Subroutine of explainStoreExplanation
// Re-root the tree containing x, in such a way that
// the new root is x itself
//
void Explainer::reRootOn(ERef x) {
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

        // Move the two pointers
        p = parent;
        parent = grandparent;
    }
}

vec<PtAsgn> Explainer::explain(opensmt::pair<ERef,ERef> nodePair) {

#ifdef EXPLICIT_CONGRUENCE_EXPLANATIONS
    congruences.clear();
#endif

    DupChecker dupChecker(dcd);
    vec<PtAsgn> explanation;
    PendingQueue exp_pending;
    exp_pending.push(nodePair);
    while ( exp_pending.size() > 0 ) {

        ERef p = exp_pending.last().first;
        ERef q = exp_pending.last().second;
        exp_pending.pop();

        if (p == q) continue;

        ERef w = NCA(p, q);
        if (w == ERef_Undef) {
            throw OsmtInternalException("Equality explanation queried for terms not in same equivalence class");
        }

        explainAlongPath(p, w, explanation, exp_pending, dupChecker);
        explainAlongPath(q, w, explanation, exp_pending, dupChecker);
    }
    cleanup();
    return explanation;
}

//
// Produce an explanation between nodes x and y
// Wrapper for expExplain
//
vec<PtAsgn> Explainer::explain(ERef x, ERef y)
{
    return explain({x, y});
}

void Explainer::cleanup() {
    // Destroy the eq classes of the explanation
    for (int i = exp_cleanup.size()-1; i >= 0; i--) {
        auto x = exp_cleanup[i];
        getEnode(x).setExpRoot(x);
    }
    exp_cleanup.clear();
}

//
// Subroutine of explain
// A step of explanation for x and y
//
void Explainer::explainAlongPath(ERef x, ERef y, vec<PtAsgn> &outExplanation, PendingQueue &pendingExplanations, DupChecker& dc) {
    auto v  = findAndCompress(x);
    // Why this? Not in the pseudo code!
    auto to = findAndCompress(y);

    while ( v != to ) {
        ERef p = getEnode(v).getExpParent();
        assert(p != ERef_Undef);
        PtAsgn edgeExplanation = explainEdge(v, p, pendingExplanations, dc);
        if (edgeExplanation != PtAsgn_Undef) {
            outExplanation.push(edgeExplanation);
        }
        v = findAndCompress(p);
    }
}

/**
 * Enqueue the equivalence query of two n-ary terms x(a1,...,an) and y(a1,...,an).
 * Preconditions: x and y are n-ary terms of the same function symbol.
 * @param x an n-ary term over function symbol f
 * @param y an n-ary term over function symbol f
 * @param exp_pending the vector where to place the equivalences to be queried.
 */
void Explainer::enqueueArguments(ERef x, ERef y, PendingQueue &exp_pending) {
    // No explanation needed if they are the same
    if (x == y) {
        return;
    }
    // Recursively enqueue the explanations for the args
    Enode const & xnode = getEnode(x);
    Enode const & ynode = getEnode(y);

    assert(xnode.getSize() == ynode.getSize());
    for (uint32_t i = 0; i < xnode.getSize(); ++i) {
        ERef xchild = xnode[i];
        ERef ychild = ynode[i];
        if (xchild != ychild) {
            exp_pending.push({xchild, ychild});
        }
    }
}

PtAsgn Explainer::explainEdge(const ERef v, const ERef p, PendingQueue &exp_pending, DupChecker &dc) {
    assert(getEnode(v).getExpParent() == p);
    PtAsgn r = getEnode(v).getExpReason();

    PtAsgn expl = PtAsgn_Undef;

    if (r.tr != PTRef_Undef) {
        // Not a congruence edge
        if (not dc.isDup(r.tr)) {
            expl = r;
            dc.storeDup(r.tr);
        }
    } else {
        // A congruence edge
        // This means that the edge is linking nodes
        // like (v)f(a1,...,an) (p)f(b1,...,bn), and that
        // a1,...,an = b1,...bn. For each pair ai,bi
        // we have therefore to compute the reasons
        assert(getEnode(v).getSymbol() == getEnode(p).getSymbol());
        enqueueArguments(v, p, exp_pending);
    }
    makeUnion(v, p);
    return expl;
}

void Explainer::makeUnion(ERef x, ERef y) {
    // Unions are always between a node and its parent
    assert(getEnode(x).getExpParent() == y);
    // Retrieve the representant for the explanation class for x and y
    ERef x_exp_root = findAndCompress(x);
    ERef y_exp_root = findAndCompress(y);

    // No need to merge elements of the same class
    if ( x_exp_root == y_exp_root )
        return;
    // Save highest node. It is always the node of the parent,
    // as it is closest to the root of the explanation tree
    getEnode(x_exp_root).setExpRoot(y_exp_root);

    // Keep track of this union
    exp_cleanup.push(x_exp_root);
    exp_cleanup.push(y_exp_root);
}

//
// Find the representant of x's equivalence class
// and meanwhile do path compression
//
ERef Explainer::findAndCompress(ERef x) {
    // If x is the root, return x
    if (getEnode(x).getExpRoot() == x) return x;
    // Recurse
    ERef exp_root = findAndCompress(getEnode(x).getExpRoot());
    // Path compression
    if (exp_root != getEnode(x).getExpRoot()) {
        getEnode(x).setExpRoot(exp_root);
        exp_cleanup.push(x);
    }
    return exp_root;
}

//
// Explain Nearest Common Ancestor
//

ERef Explainer::NCA(ERef x, ERef y) {
    // Increase time stamp
    ++time_stamp;

    auto h_x = findAndCompress(x);
    auto h_y = findAndCompress(y);

    while ( h_x != h_y ) {
        assert(h_x == ERef_Undef || getEnode(h_x).getExpTimeStamp() <= time_stamp);
        assert(h_y == ERef_Undef || getEnode(h_y).getExpTimeStamp() <= time_stamp);
        if ( h_x != ERef_Undef ) {
            // We reached a node already marked by h_y
            if (getEnode(h_x).getExpTimeStamp() == time_stamp) {
                return h_x;
            }

            // Mark the node and move to the next
            if (getEnode(h_x).getExpParent() != h_x) {
                getEnode(h_x).setExpTimeStamp(time_stamp);
                h_x = getEnode(h_x).getExpParent();
            }
        }
        if ( h_y != ERef_Undef ) {
            // We reached a node already marked by h_x
            if (getEnode(h_y).getExpTimeStamp() == time_stamp) {
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
// Undoes the effect of storeExplanation
// No need for enodes
//
void Explainer::removeExplanation() {
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

PtAsgn InterpolatingExplainer::explainEdge(ERef from, ERef to, PendingQueue &exp_pending, DupChecker &dc) {
    PtAsgn expl = Explainer::explainEdge(from, to, exp_pending, dc);
    const Enode& from_node = getEnode(from);
    const Enode& to_node = getEnode(to);
    cgraph->addCNode( from_node.getTerm() );
    cgraph->addCNode( to_node.getTerm() );
    cgraph->addCEdge( from_node.getTerm(), to_node.getTerm(), from_node.getExpReason().tr);
    return expl;
}

vec<PtAsgn> InterpolatingExplainer::explain(ERef x, ERef y) {
    cgraph.reset(new CGraph());
    cgraph->setConf(getEnode(x).getTerm(), getEnode(y).getTerm());
    return Explainer::explain(x,y);
}
