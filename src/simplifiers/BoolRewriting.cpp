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
#ifdef PRODUCE_PROOF // MB: TODO: move this elsewhere
    // copy the partition of tr to the resulting new term
    logic.transferPartitionMembership(tr, new_tr);
#endif
    return new_tr;
}

