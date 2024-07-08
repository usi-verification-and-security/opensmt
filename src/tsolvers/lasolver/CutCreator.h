/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *                      Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_CUTCREATOR_H
#define OPENSMT_CUTCREATOR_H

#include "PTRef.h"
#include "Polynomial.h"
#include "Real.h"
#include "SparseMatrix.h"
#include "TypeUtils.h"

class CutCreator {
private:
    std::function<opensmt::Real(PTRef)> varValue;

    opensmt::Real evaluate(PTRef var) const { return varValue(var); }

public:
    explicit CutCreator(std::function<opensmt::Real(PTRef)> && varValue) : varValue(std::move(varValue)) {}

    using Cut = opensmt::pair<SparseColMatrix::TermVec, opensmt::Real>;
    using ColumnMapping = std::vector<PTRef>;
    Cut makeCut(SparseLinearSystem && constraints, ColumnMapping const &);
};

#endif // OPENSMT_CUTCREATOR_H
