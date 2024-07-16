/*
 * Copyright (c) 2021 - 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ArrayTheory.h"

#include "ArrayHelpers.h"
#include "Rewritings.h"

PTRef ArrayTheory::preprocessAfterSubstitutions(PTRef fla, PreprocessingContext const &) {
    // TODO: simplify select over store on the same index
    fla = opensmt::rewriteDistincts(getLogic(), fla);
    fla = instantiateReadOverStore(getLogic(), fla);
    return fla;
}
