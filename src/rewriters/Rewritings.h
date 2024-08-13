/*
 * Copyright (c) 2024 Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_REWRITINGS_H
#define OPENSMT_REWRITINGS_H

#include <logics/ArithLogic.h>
#include <pterms/PTRef.h>

#include <optional>

namespace opensmt {
PTRef rewriteDistincts(Logic & logic, PTRef fla);

PTRef rewriteDistinctsKeepTopLevel(Logic & logic, PTRef fla);

PTRef rewriteDivMod(ArithLogic & logic, PTRef fla);

std::optional<PTRef> tryGetOriginalDivModTerm(ArithLogic & logic, PTRef term);
} // namespace opensmt

#endif // OPENSMT_REWRITINGS_H
