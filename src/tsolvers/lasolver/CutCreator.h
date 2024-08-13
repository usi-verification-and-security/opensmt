/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *                      Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_CUTCREATOR_H
#define OPENSMT_CUTCREATOR_H

#include "Polynomial.h"
#include "SparseMatrix.h"

#include <common/Real.h>
#include <common/TypeUtils.h>
#include <pterms/PTRef.h>

namespace opensmt {
class CutCreator {
public:
    explicit CutCreator(std::function<Real(PTRef)> && varValue) : varValue(std::move(varValue)) {}

    using Cut = pair<SparseColMatrix::TermVec, Real>;
    using ColumnMapping = std::vector<PTRef>;
    Cut makeCut(SparseLinearSystem && constraints, ColumnMapping const &);

private:
    Real evaluate(PTRef var) const { return varValue(var); }

    std::function<Real(PTRef)> varValue;
};
} // namespace opensmt

#endif // OPENSMT_CUTCREATOR_H
