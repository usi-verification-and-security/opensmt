//
// Created by Martin Blicha on 04.05.21.
//

#include "DistinctRewriter.h"
#include "TreeOps.h"

PTRef rewriteDistinctsKeepTopLevel(Logic & logic, PTRef fla) {
    vec<PTRef> topLevelConjuncts = ::topLevelConjuncts(logic, fla);
    KeepTopLevelDistinctRewriter::TopLevelDistincts topLevelDistincts;
    for (PTRef conj : topLevelConjuncts) {
        if (logic.isDisequality(conj)) { topLevelDistincts.insert(conj); }
    }
    return KeepTopLevelDistinctRewriter(logic, std::move(topLevelDistincts)).rewrite(fla);
}
