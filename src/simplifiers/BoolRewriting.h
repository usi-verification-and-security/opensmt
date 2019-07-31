//
// Created by Martin Blicha on 20.10.18.
//

#ifndef OPENSMT_BOOLREWRITING_H
#define OPENSMT_BOOLREWRITING_H

#include <PTRef.h>
#include <vector>
#include <unordered_map>
#include <Logic.h>

class Logic;

void computeIncomingEdges(const Logic& logic, PTRef tr, Map<PTRef,int,PTRefHash>& PTRefToIncoming);

PTRef rewriteMaxArityAggresive(Logic & logic, PTRef root);

PTRef rewriteMaxArityClassic(Logic & logic, PTRef root);

PTRef simplifyUnderAssignment(Logic & logic, PTRef root);

PTRef simplifyUnderAssignment_Aggressive(PTRef root, Logic & logic);

std::vector<PTRef> getPostOrder(PTRef root, Logic& logic);

std::unordered_map<PTRef, PTRef, PTRefHash> getImmediateDominators(PTRef root, Logic & logic);

template<typename T>
PTRef mergeAndOrArgs(Logic & logic, PTRef tr, Map<PTRef,PTRef,PTRefHash>& cache, T doNotMerge)
{
    assert(logic.isAnd(tr) || logic.isOr(tr));
    const Pterm& t = logic.getPterm(tr);
    SymRef sr = t.symb();
    vec<PTRef> new_args;
    bool changed = false;
    for (int i = 0; i < t.size(); i++) {
        PTRef subst = cache[t[i]];
        changed |= (subst != t[i]);
        if (logic.getSymRef(t[i]) != sr) {
            new_args.push(subst);
            continue;
        }
        if (doNotMerge(t[i])) {
            new_args.push(subst);
            continue;
        }
        if (logic.getSymRef(subst) == sr) {
            changed = true;
            const Pterm& substs_t = logic.getPterm(subst);
            for (int j = 0; j < substs_t.size(); j++)
                new_args.push(substs_t[j]);
        }
        else {
            new_args.push(subst);
        }
    }
    if (!changed) { return tr; }
    PTRef new_tr = (sr == logic.getSym_and() ? logic.mkAnd(new_args) : logic.mkOr(new_args));
    return new_tr;
}


template<typename T>
PTRef rewriteMaxArity(Logic & logic, const PTRef root, T doNotRewrite) {
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
        const Pterm& t = logic.getPterm(tr);
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
            result = ::mergeAndOrArgs(logic, tr, cache, doNotRewrite);
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

#endif //OPENSMT_BOOLREWRITING_H
