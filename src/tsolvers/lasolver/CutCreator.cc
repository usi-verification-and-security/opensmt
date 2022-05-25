/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "CutCreator.h"

namespace {
SparseColMatrix identityMatrix(uint32_t size) {
    SparseColMatrix id(RowCount{size}, ColumnCount{size});
    for (uint32_t i = 0; i < size; ++i) {
        SparseColMatrix::ColumnPolynomial poly;
        poly.addTerm(IndexType{i}, 1);
        id.setColumn(ColIndex{i}, std::move(poly));
    }
    return id;
}

void negateColumn(SparseColMatrix & A, ColIndex colIndex, SparseColMatrix & U) {
    A[colIndex].negate();
    U[colIndex].negate();
}

void swapColumns(SparseColMatrix & A, ColIndex pivotIndex, ColIndex otherIndex, SparseColMatrix & U) {
    assert(pivotIndex != otherIndex);
    A.swapCols(pivotIndex, otherIndex);
    U.swapCols(pivotIndex, otherIndex);
}

void addColumnMultiple(SparseColMatrix & A, ColIndex colFrom, opensmt::Real const & multiple, ColIndex colTo, SparseColMatrix & U) {
    A[colTo].add(A[colFrom], multiple);
    // For U we do the inverse operation: colFrom += -multiple * colTo
    U[colFrom].add(U[colTo], -multiple);
}

/*
 * Normalizes row so that all entries to the right of pivot are zero.
 * Returns true if the pivot is non-zero.
 */
bool normalizeRow(SparseColMatrix & A, RowIndex rowIndex, ColIndex pivotIndex, SparseColMatrix & U) {
    // Collect all columns with non-zero entry at given row; ensure they are positive
    std::vector<ColIndex> activeColumns;
    auto size = A.colCount();
    activeColumns.reserve(size - pivotIndex);
    for (uint32_t col = pivotIndex; col < size; ++col) {
        if (A[col].isFirst(rowIndex)) {
            activeColumns.push_back(ColIndex{col});
            if (A[col].getFirstCoeff().sign() < 0) {
                negateColumn(A, ColIndex{col}, U);
            }
        }
    }
    if (activeColumns.empty()) { return false; }

    // Reduce the set of active columns until there is only a single one.
    // Current implementation: Find minimal value, reduce others, and repeat
    // Alternative possiblity: Rosser's algorithm (see Yices), which uses largest values to for reductions
    while (activeColumns.size() > 1) {
        auto it = std::min_element(activeColumns.begin(), activeColumns.end(), [&A](ColIndex first, ColIndex second) {
            assert(A[first].getFirstCoeff().sign() > 0 and A[second].getFirstCoeff().sign() > 0);
            return A[first].getFirstCoeff() < A[second].getFirstCoeff();
        });
        std::iter_swap(it, activeColumns.begin());
        // Now the index of column with smallest value is first in activeColumns
        auto smallestValue = A[activeColumns[0]].getFirstCoeff();
        uint32_t nextColIndex = 1;
        while (nextColIndex < activeColumns.size()) {
            auto const & nextCol = A[activeColumns[nextColIndex]];
            auto quotient = -fastrat_fdiv_q(nextCol.getFirstCoeff(), smallestValue);
            assert(not quotient.isZero());
            addColumnMultiple(A, activeColumns[0], quotient, activeColumns[nextColIndex], U);
            if (not nextCol.isFirst(rowIndex)) { // the entry in this column is zero now, remove the column from active set
                std::swap(activeColumns[nextColIndex], activeColumns.back());
                activeColumns.pop_back();
                // do not advance index!
            } else { // the entry in this column is not zero yet, just continue with next column
                ++nextColIndex;
            }
        }
    }
    // Single active column left, move it to the pivot's position
    assert(activeColumns.size() == 1);
    if (activeColumns[0] != pivotIndex) {
        swapColumns(A, activeColumns[0], pivotIndex, U);
    }
    return true;
}

void reduceToTheLeft(SparseColMatrix & A, RowIndex rowIndex, ColIndex pivotIndex, SparseColMatrix & U) {
    auto const & pivotCol = A[pivotIndex];
    assert(pivotCol.isFirst(rowIndex));
    auto const & pivotVal = pivotCol.getFirstCoeff();
    for (uint32_t col = 0; col < pivotIndex; ++col) {
        auto const * otherVal = A[col].tryGetCoeffFor(rowIndex);
        if (not otherVal) { continue; }
        auto quotient = -fastrat_fdiv_q(*otherVal, pivotVal);
        if (not quotient.isZero()) {
            addColumnMultiple(A, pivotIndex, quotient, ColIndex{col}, U);
        }
    }
}
}


CutCreator::Cut CutCreator::makeCut(SparseLinearSystem && system, ColumnMapping const & columnMapping) {
    auto & A = system.A;

    assert(A.colCount() == columnMapping.size());
    uint32_t varCount = A.colCount();

    // Get the values of the variables
    std::vector<opensmt::Real> varValues;
    varValues.reserve(varCount);
    for (uint32_t col = 0; col < varCount; ++col) {
        PTRef var = columnMapping[col];
        varValues.push_back(evaluate(var));
    }

    // We perform column operations on A to transform it to Hermite Normal Form
    // At the same time we record the inverse operations in U
    // We maintain the invariant that A'*U' = A; starting with U:=I, the identity matrix
    // We actually maintain the transpose of U' as column matrix and not U' as row matrix
    uint32_t cols = A.colCount();
    uint32_t rows = A.rowCount();
    SparseColMatrix UT = identityMatrix(cols);

    uint32_t pivotCol = 0;
    for (uint32_t currRow = 0; currRow < rows and pivotCol < cols; ++currRow) {
        // First make sure the current row conforms to the lower triangular form
        bool hasPivot = normalizeRow(A, RowIndex{currRow}, ColIndex{pivotCol}, UT);
        if (not hasPivot) {
            // a row that is linearly dependent on rows above it; skip it and continue with the next row
            // DO NOT INCREMENT PIVOT!
            continue;
        }
        // Now make sure it conforms to HNF rule that elements to the left of pivot are smaller and positive
        reduceToTheLeft(A, RowIndex{currRow}, ColIndex{pivotCol}, UT);

        // At this point the pivot column will no longer be used for any colum operations.
        // That means that the corresponding row in U will not change after this point.
        // We can check its feasibility at this point already
        auto const & row = UT[pivotCol];
        auto product = row.product(varValues);
        if (not product.isInteger()) {
            return {row.toVector(), product};
        }
        // DO NOT FORGET TO INCREMENT PIVOT!
        ++pivotCol;
    }
    return {};
}

