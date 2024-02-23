/*
 * Copyright (c) 2021 - 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ArrayTheory.h"

#include "ArrayHelpers.h"
#include "DistinctRewriter.h"

PTRef ArrayTheory::preprocessAfterSubstitutions(PTRef fla, PreprocessingContext const & context) {
    if (context.perPartition) { throw OsmtInternalException("Interpolation not supported for logics with arrays yet"); }
    // TODO: simplify select over store on the same index
    fla = rewriteDistincts(getLogic(), fla);
    fla = instantiateReadOverStore(getLogic(), fla);
    return fla;
}
