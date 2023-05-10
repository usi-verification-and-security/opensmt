/*
* Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
*
*  SPDX-License-Identifier: MIT
*
 */

#include "SubstitutionUtils.h"

#include "Substitutor.h"
#include "TreeOps.h"

#include <stack>
#include <iostream>

namespace {
auto reversedTopologicalOrder(VecMap<PTRef, PTRef, PTRefHash> const & dependencies) {
    std::vector<PTRef> order;
    std::stack<std::pair<bool,PTRef>> worklist;
    vec<PTRef> nodes;
    dependencies.getKeys(nodes);
    std::unordered_set<PTRef, PTRefHash> visited;
    auto isVisited = [&visited](PTRef ref) { return visited.find(ref) != visited.end(); };
    for (PTRef node : nodes) {
        if (not isVisited(node)) {
            worklist.emplace(false, node);
        }
        while (not worklist.empty()) {
            auto current = worklist.top();
            worklist.pop();
            if (current.first) {
                order.push_back(current.second);
                continue;
            }
            if (isVisited(current.second)) {
                continue;
            }
            visited.insert(current.second);
            worklist.emplace(true, current.second);

            for (PTRef dependency : dependencies[current.second]) {
                if (not isVisited(dependency)) {
                    worklist.emplace(false, dependency);
                }
            }
        }
    }
    return order;
}
}

void substitutionsTransitiveClosure(Logic::SubstMap & substs, Logic & logic) {
    auto const & keys = substs.getKeys();
    auto isKey = [&](PTRef term) { return substs.has(term); };
    VecMap<PTRef, PTRef, PTRefHash> dependencies;
    for (PTRef key : keys) {
        PTRef value = substs[key];
        auto otherKeysInValue = matchingSubTerms(logic, value, isKey);
        assert(std::none_of(otherKeysInValue.begin(), otherKeysInValue.end(), [key](PTRef otherKey) { return otherKey == key; }));
        dependencies.insert(key, otherKeysInValue);
    }
    auto ordering = reversedTopologicalOrder(dependencies);

    for (PTRef key : ordering) {
        PTRef & val = substs[key];
        PTRef oldVal = val;
        PTRef newVal = Substitutor(logic, substs).rewrite(oldVal);
        val = newVal;
    }
}