/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_CUTCREATOR_H
#define OPENSMT_CUTCREATOR_H

#include "Real.h"
#include "Polynomial.h"
#include "SparseMatrix.h"
#include "PTRef.h"
#include "TypeUtils.h"

class CutCreator {
private:
    std::function<FastRational(PTRef)> varValue;

    FastRational evaluate(PTRef var) const { return varValue(var); }
public:


    explicit CutCreator(std::function<FastRational(PTRef)> && varValue) : varValue(std::move(varValue)) {}

    using Cut = opensmt::pair<SparseColMatrix::TermVec, FastRational>;
    using ColumnMapping = std::vector<PTRef>;
    Cut makeCut(SparseLinearSystem && constraints, ColumnMapping const &);
};


#endif //OPENSMT_CUTCREATOR_H
