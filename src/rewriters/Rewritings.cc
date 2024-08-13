/*
 * Copyright (c) 2024 Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "Rewritings.h"
#include "DistinctRewriter.h"
#include "DivModRewriter.h"

#include <common/TreeOps.h>

namespace opensmt {
PTRef rewriteDistincts(Logic & logic, PTRef fla) {
    return DistinctRewriter(logic).rewrite(fla);
}

PTRef rewriteDistinctsKeepTopLevel(Logic & logic, PTRef fla) {
    vec<PTRef> topLevelConjuncts = opensmt::topLevelConjuncts(logic, fla);
    KeepTopLevelDistinctRewriter::TopLevelDistincts topLevelDistincts;
    for (PTRef conj : topLevelConjuncts) {
        if (logic.isDisequality(conj)) { topLevelDistincts.insert(conj); }
    }
    return KeepTopLevelDistinctRewriter(logic, std::move(topLevelDistincts)).rewrite(fla);
}

PTRef rewriteDivMod(ArithLogic & logic, PTRef term) {
    return DivModRewriter(logic).rewrite(term);
}

std::optional<PTRef> tryGetOriginalDivModTerm(ArithLogic & logic, PTRef tr) {
    if (not logic.isVar(tr)) return std::nullopt; // Only variables can match
    auto symName = std::string_view(logic.getSymName(tr));
    if (symName.compare(0, DivModConfig::divPrefix.size(), DivModConfig::divPrefix) == 0) {
        return DivModConfig::getDivTermFor(logic, tr);
    }
    if (symName.compare(0, DivModConfig::modPrefix.size(), DivModConfig::modPrefix) == 0) {
        return DivModConfig::getModTermFor(logic, tr);
    }
    return std::nullopt;
}
} // namespace opensmt
