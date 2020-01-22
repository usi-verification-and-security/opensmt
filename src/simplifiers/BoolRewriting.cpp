//
// Created by Martin Blicha on 20.10.18.
//

#include "BoolRewriting.h"
#include "Logic.h"
#include <unordered_set>

// Replace subtrees consisting only of ands / ors with a single and / or term.
// Search a maximal section of the tree consisting solely of ands / ors.  The
// root of this subtree is called and / or root.  Collect the subtrees rooted at
// the leaves of this section, and create a new and / or term with the leaves as
// arguments and the parent of the and / or tree as the parent.
//
// However, we will do this in a clever way so that if a certain
// term appears as a child in more than one term, we will not flatten
// that structure.
//
void computeIncomingEdges(const Logic& logic, PTRef tr, Map<PTRef,int,PTRefHash>& PTRefToIncoming)
{
    class pi {
    public:
        PTRef x;
        bool done;
        pi(PTRef x_) : x(x_), done(false) {}
    };

    assert(tr != PTRef_Undef);
    vec<pi*> unprocessed_ptrefs;
    unprocessed_ptrefs.push(new pi(tr));
    while (unprocessed_ptrefs.size() > 0) {
        pi* pi_ptr = unprocessed_ptrefs.last();
        if (PTRefToIncoming.has(pi_ptr->x)) {
            PTRefToIncoming[pi_ptr->x]++;
            unprocessed_ptrefs.pop();
            delete pi_ptr;
            continue;
        }
        bool unprocessed_children = false;
        if (logic.isBooleanOperator(pi_ptr->x) && pi_ptr->done == false) {
            const Pterm& t = logic.getPterm(pi_ptr->x);
            for (int i = 0; i < t.size(); i++) {
                // push only unprocessed Boolean operators
                if (!PTRefToIncoming.has(t[i])) {
                    unprocessed_ptrefs.push(new pi(t[i]));
                    unprocessed_children = true;
                } else {
                    PTRefToIncoming[t[i]]++;
                }
            }
            pi_ptr->done = true;
        }
        if (unprocessed_children)
            continue;

        unprocessed_ptrefs.pop();
        // All descendants of pi_ptr->x are processed
        assert(logic.isBooleanOperator(pi_ptr->x) || logic.isAtom(pi_ptr->x));
        assert(!PTRefToIncoming.has(pi_ptr->x));
        PTRefToIncoming.insert(pi_ptr->x, 1);
        delete pi_ptr;
    }
}

PTRef rewriteMaxArityClassic(Logic & logic, PTRef root) {
    Map<PTRef,int,PTRefHash> PTRefToIncoming;
    computeIncomingEdges(logic, root, PTRefToIncoming);
    return rewriteMaxArity(logic, root,
            [&PTRefToIncoming](PTRef candidate)
            {
                assert(PTRefToIncoming.has(candidate) && PTRefToIncoming[candidate] >= 1);
                return PTRefToIncoming[candidate] > 1;
            });
}

PTRef rewriteMaxArityAggresive(Logic & logic, PTRef root) {
    return rewriteMaxArity(logic, root,
                    [](PTRef candidate) { return false;});
}

namespace {
struct PtLit {
    PTRef var;
    bool sign;
};

PtLit operator ~(PtLit lit) { return PtLit{lit.var, !lit.sign};}

bool isTerminal(const Logic & logic, PTRef fla) {
//    return logic.isLit(fla);
/* MB: The above does NOT work, because of Tseitin literals,
 * which are literals from proof point of view, but not not literals as PTRefs
 * So we stop at everything which is not AND or OR.
 * */
    return !(logic.isAnd(fla) || logic.isOr(fla));
}

PtLit decomposeLiteral(const Logic & logic, PTRef lit) {
    assert(isTerminal(logic, lit));
    bool sgn = false;
    while (logic.getSymRef(lit) == logic.getSym_not()) {
        lit = logic.getPterm(lit)[0];
        sgn = !sgn;
    }
    return PtLit{lit, sgn};
}

PTRef _simplifyUnderAssignment(Logic & logic, PTRef root,
                               const Map<PTRef, int, PTRefHash> & PTRefToIncoming,
                               std::vector<PtLit> assignment,
                               Map<PTRef, PTRef, PTRefHash> & cache
) {
    if (!logic.isAnd(root) && !logic.isOr(root)) {
        assert(false); // MB: should not be called for anything else
        return root;
    }
    assert(!cache.has(root));
    bool isAnd = logic.isAnd(root);
    vec<PTRef> newargs;
    const Pterm & term = logic.getPterm(root);
    std::vector<PTRef> literals;
    std::vector<PTRef> owning_children;
    std::vector<PTRef> non_owning_children;
    for (int i = 0; i < term.size(); ++i) {
        if (isTerminal(logic, term[i])) {
            literals.push_back(term[i]);
            continue;
        }
        assert(PTRefToIncoming.has(term[i]));
        assert(PTRefToIncoming[term[i]] >= 1);
        if (PTRefToIncoming[term[i]] > 1) {
            non_owning_children.push_back(term[i]);
        }
        else{
            owning_children.push_back(term[i]);
        }
    }
    // process the literals
    for (PTRef lit : literals) {
        assert(!cache.has(lit));
        PtLit decLit = decomposeLiteral(logic, lit);
        auto it = std::find_if(assignment.begin(), assignment.end(), [decLit](PtLit assign) {
            return assign.var == decLit.var;
        });
        if (it == assignment.end()) {
            assignment.push_back(isAnd ? decLit : ~decLit);
            newargs.push(lit);
        } else {
            assert(decLit.var == it->var);
            if (decLit.sign == it->sign) {
                // this literal is evaluated to true
                if (!isAnd) { return logic.getTerm_true(); }
            } else {
                // this literal is evaluated to false
                if (isAnd) { return logic.getTerm_false(); }
            }
        }
    }
    for (PTRef owning_child : owning_children) {
        assert(!cache.has(owning_child));
        newargs.push(_simplifyUnderAssignment(logic, owning_child, PTRefToIncoming, assignment, cache));
    }
    for (PTRef non_owning_child : non_owning_children) {
        // cannot simplify under assignment if somebody else is also pointing to this
        if (cache.has(non_owning_child)) {
            newargs.push(cache[non_owning_child]);
        } else {
            PTRef new_child = _simplifyUnderAssignment(logic, non_owning_child, PTRefToIncoming, {}, cache);
            newargs.push(new_child);
            cache.insert(non_owning_child, new_child);
        }

    }
    return isAnd ? logic.mkAnd(newargs) : logic.mkOr(newargs);
}
}

PTRef simplifyUnderAssignment(Logic & logic, PTRef root) {
    Map<PTRef, int, PTRefHash> incomingEdges;
    ::computeIncomingEdges(logic, root, incomingEdges);
    Map<PTRef, PTRef, PTRefHash> cache;
    return _simplifyUnderAssignment(logic, root, incomingEdges, {},  cache);
}

namespace{
template<typename C, typename T>
bool contains(C const & container, T el) {
    return container.find(el) != container.end();
}

void walkDFS(PTRef node, std::unordered_set<PTRef, PTRefHash> & visited, std::vector<PTRef>& order, Logic & logic) {
    visited.insert(node);
    Pterm const & term = logic.getPterm(node);
    for (int i = 0; i < term.size(); ++i) {
        assert(node.x > term[i].x);
        if (!contains(visited, term[i])) {
            walkDFS(term[i], visited, order, logic);
        }
    }
    order.push_back(node);
}


void update_idom(PTRef node, PTRef parent, std::unordered_map<PTRef, PTRef, PTRefHash>& idom) {
    //  relies on the fact that child has to be always allocated before parent, so child's PTRef is smaller
    assert(contains(idom, node));
    assert(node.x < parent.x);
    PTRef old_idom = idom.at(node);
    // walk up the DAG until you find common ancestor
    PTRef f1 = old_idom;
    PTRef f2 = parent;
    while (f1 != f2) {
        while (f1.x < f2.x) {
            assert(contains(idom, f1));
            f1 = idom.at(f1);
        }
        while (f2.x < f1.x) {
            assert(contains(idom, f2));
            f2 = idom.at(f2);
        }
    }
    idom[node] = f1;
}
}

std::vector<PTRef> getPostOrder(PTRef root, Logic& logic) {
    std::vector<PTRef> res;
    std::unordered_set<PTRef, PTRefHash> seen;
    walkDFS(root, seen, res, logic);
    return res;
}

std::unordered_map<PTRef, PTRef, PTRefHash> getImmediateDominators(PTRef root, Logic & logic) {
    std::unordered_map<PTRef, PTRef, PTRefHash> idom;
    idom[root] = root;
    auto postOrder = getPostOrder(root, logic);
    for(auto it = postOrder.rbegin(); it != postOrder.rend(); ++it) { // iterating in REVERSE post order
        PTRef current = *it;
        assert(contains(idom, current));
        // update idoms of all children
        Pterm const & term = logic.getPterm(current);
        for(int i = 0; i < term.size(); ++i) {
            if (contains(idom, term[i])) {
                update_idom(term[i], current, idom);
            }
            else {
                idom[term[i]] = current;
            }
        }
    }
    return idom;
}

namespace{
PTRef simplifyUnderAssignment_Aggressive(PTRef node, Logic & logic, std::unordered_map<PTRef, PTRef, PTRefHash> const & dominators,
        std::unordered_map<PTRef, std::vector<PtLit>, PTRefHash>& assignments,
        std::unordered_map<PTRef, PTRef, PTRefHash> & cache
        ) {
    if (!logic.isAnd(node) && !logic.isOr(node)) {
        assert(false); // MB: should not be called for anything else
        return node;
    }
    assert(contains(dominators, node));
    assert(contains(assignments, dominators.at(node)));
    assert(!contains(cache, node));
    const Pterm & term = logic.getPterm(node);
    std::vector<PTRef> literals;
    std::vector<PTRef> connective_children;
    for (int i = 0; i < term.size(); ++i) {
        if (isTerminal(logic, term[i])) {
            literals.push_back(term[i]);
        }
        else{
            connective_children.push_back(term[i]);
        }
    }
    bool isAnd = logic.isAnd(node);
    vec<PTRef> newargs;
    // this is the assignment that is propagated to me and I can use it to simplify myself and my children
    assert(assignments.find(dominators.at(node)) != assignments.end());
    std::vector<PtLit> assignment = assignments.at(dominators.at(node));
    // process the literals
    for (PTRef lit : literals) {
        assert(!contains(cache, lit));
        PtLit decLit = decomposeLiteral(logic, lit);
        auto it = std::find_if(assignment.begin(), assignment.end(), [decLit](PtLit assign) {
            return assign.var == decLit.var;
        });
        if (it == assignment.end()) {
            assignment.push_back(isAnd ? decLit : ~decLit);
            newargs.push(lit);
        } else {
            assert(decLit.var == it->var);
            if (decLit.sign == it->sign) {
                // this literal is evaluated to true
                if (!isAnd) { return logic.getTerm_true(); }
                // else isAND -> simply ignore this conjunct
            } else {
                // this literal is evaluated to false
                if (isAnd) { return logic.getTerm_false(); }
                // else isOR -> simply ignore this disjunct
            }
        }
    }
    // set my assignment and recurse on children
    assignments[node] = std::move(assignment);

    for (PTRef child : connective_children) {
        if (contains(cache, child)) {
            newargs.push(cache[child]);
        } else {
            PTRef new_child = simplifyUnderAssignment_Aggressive(child, logic, dominators, assignments, cache);
            newargs.push(new_child);
            cache[child] = new_child;
        }
    }
    // after we are done with this node, we don't need to remember its assignment anymore
    assignments.erase(node);
    return isAnd ? logic.mkAnd(newargs) : logic.mkOr(newargs);
}
}

PTRef simplifyUnderAssignment_Aggressive(PTRef root, Logic & logic) {
    auto idom = getImmediateDominators(root, logic);
    std::unordered_map<PTRef, std::vector<PtLit>, PTRefHash> assignments;
    assignments[root] = {};
    std::unordered_map<PTRef, PTRef, PTRefHash> cache;
    return simplifyUnderAssignment_Aggressive(root, logic, idom, assignments, cache);
}
