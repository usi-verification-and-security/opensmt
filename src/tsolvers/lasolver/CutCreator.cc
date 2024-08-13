/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "CutCreator.h"

namespace opensmt {
CutCreator::Cut CutCreator::makeCut(SparseLinearSystem && system, ColumnMapping const & columnMapping) {
    auto & matrixA = system.A;

    assert(matrixA.colCount() == columnMapping.size());
    uint32_t varCount = matrixA.colCount();

    auto [matrixU, dim] = HermiteNormalForm()(std::move(matrixA));

    // Get the values of the variables
    std::vector<Real> varValues;
    varValues.reserve(varCount);
    for (uint32_t col = 0; col < varCount; ++col) {
        PTRef var = columnMapping[col];
        varValues.push_back(evaluate(var));
    }
    // Now check every row of U for infeasibility: if the cross product of the row and vector of variable values is
    // not an integer, the row represents an infeasible constraint
    for (uint32_t rowIndex = 0; rowIndex < dim; ++rowIndex) {
        auto const & row = matrixU[rowIndex];
        auto product = row.product(varValues);
        if (not product.isInteger()) { return {row.toVector(), product}; }
    }
    return {};
}
} // namespace opensmt
