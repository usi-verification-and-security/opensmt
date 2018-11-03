//
// Created by Martin Blicha on 20.10.18.
//

#include "BoolRewriting.h"
#include "Logic.h"

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

PTRef rewriteMaxArity(Logic & logic, PTRef root, const Map<PTRef,int,PTRefHash>& PTRefToIncoming)
{
    vec<PTRef> unprocessed_ptrefs;
    unprocessed_ptrefs.push(root);
    Map<PTRef,PTRef,PTRefHash> cache;

    while (unprocessed_ptrefs.size() > 0) {
        PTRef tr = unprocessed_ptrefs.last();
        if (cache.has(tr)) {
            unprocessed_ptrefs.pop();
            continue;
        }

        bool unprocessed_children = false;
        Pterm& t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); i++) {
            if (logic.isBooleanOperator(t[i]) && !cache.has(t[i])) {
                unprocessed_ptrefs.push(t[i]);
                unprocessed_children = true;
            }
            else if (logic.isAtom(t[i]))
                cache.insert(t[i], t[i]);
        }
        if (unprocessed_children)
            continue;

        unprocessed_ptrefs.pop();
        PTRef result = PTRef_Undef;
        assert(logic.isBooleanOperator(tr));

        if (logic.isAnd(tr) || logic.isOr(tr)) {
            result = ::mergePTRefArgs(logic, tr, cache, PTRefToIncoming);
        } else {
            result = tr;
        }
        assert(result != PTRef_Undef);
        assert(!cache.has(tr));
        cache.insert(tr, result);

    }
    PTRef top_tr = cache[root];
    return top_tr;
}

PTRef mergePTRefArgs(Logic & logic, PTRef tr, Map<PTRef,PTRef,PTRefHash>& cache, const Map<PTRef,int,PTRefHash>& PTRefToIncoming)
{
    assert(logic.isAnd(tr) || logic.isOr(tr));
    Pterm& t = logic.getPterm(tr);
    SymRef sr = t.symb();
    vec<PTRef> new_args;
    for (int i = 0; i < t.size(); i++) {
        PTRef subst = cache[t[i]];
        if (logic.getSymRef(t[i]) != sr) {
            new_args.push(subst);
            continue;
        }
        assert(PTRefToIncoming.has(t[i]));
        assert(PTRefToIncoming[t[i]] >= 1);
        if (PTRefToIncoming[t[i]] > 1) {
            new_args.push(subst);
            continue;
        }
        if (logic.getSymRef(subst) == sr) {
            const Pterm& substs_t = logic.getPterm(subst);
            for (int j = 0; j < substs_t.size(); j++)
                new_args.push(substs_t[j]);

        } else
            new_args.push(subst);
    }
    PTRef new_tr;
    if (sr == logic.getSym_and()) {
        new_tr = logic.mkAnd(new_args);
    }
    else {
        new_tr = logic.mkOr(new_args);
    }
    return new_tr;
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

PTRef simplifyUnderAssignment(Logic & logic, PTRef root, const Map<PTRef,int,PTRefHash>& PTRefToIncoming) {
    Map<PTRef, PTRef, PTRefHash> cache;
    return _simplifyUnderAssignment(logic, root, PTRefToIncoming, {},  cache);
}