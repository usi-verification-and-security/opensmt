/*
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ArrayTheory.h"

#include "ArrayHelpers.h"
#include "DistinctRewriter.h"
#include "TreeOps.h"


bool ArrayTheory::simplify(vec<PFRef> const & formulas, PartitionManager &, int curr)
{
    // TODO: simplify select over store on the same index
    auto & currentFrame = pfstore[formulas[curr]];
    if (this->keepPartitions()) {
        std::logic_error("Not suppported yet");
    }
    PTRef rewritten = rewriteDistincts(getLogic(), getCollateFunction(formulas, curr));
    rewritten = instantiateReadOverStore(getLogic(), rewritten);
    currentFrame.root = rewritten;
    return true;
}
