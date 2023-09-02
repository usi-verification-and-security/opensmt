/*
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ArrayTheory.h"

#include "ArrayHelpers.h"
#include "DistinctRewriter.h"

PTRef ArrayTheory::simplifyTogether(const vec<PTRef> & assertions, bool) {
    // TODO: simplify select over store on the same index
    PTRef frameFormula = getLogic().mkAnd(assertions);
    frameFormula = rewriteDistincts(getLogic(), frameFormula);
    frameFormula = instantiateReadOverStore(getLogic(), frameFormula);
    return frameFormula;
}

vec<PTRef> ArrayTheory::simplifyIndividually(const vec<PTRef> &, PartitionManager &, bool) {
    throw OsmtInternalException("Interpolation not supported for logics with arrays yet");
}
