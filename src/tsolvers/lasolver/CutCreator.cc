/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */


#include "CutCreator.h"


void ColMatrix::Col::negate() {
    this->poly.negate();
}

void ColMatrix::Col::add(Col const & other, opensmt::Real const & multiple) {
    this->poly.merge(other.poly, multiple, [](LVRef){}, [](LVRef){});
}

opensmt::Real ColMatrix::Col::product(const std::vector<FastRational> & values) const {
    opensmt::Real sum = 0;
    for (auto const & term : poly) {
        std::size_t index = term.var.x;
        assert(index < values.size());
        sum += term.coeff * values[index];
    }
    return sum;
}

PTRef ColMatrix::Col::buildCutConstraint(const std::vector<PTRef> & toVarMap, ArithLogic & logic) const {
    vec<PTRef> args; args.capacity(poly.size());
    for (auto const & term : poly) {
        args.push(logic.mkTimes(toVarMap[term.var.x], logic.mkIntConst(term.coeff)));
    }
    return logic.mkPlus(std::move(args));
}

const FastRational * ColMatrix::Col::tryGetCoeffFor(RowIndex rowIndex) const {
    LVRef bound {static_cast<uint32_t>(rowIndex.count)};
    auto it = std::lower_bound(poly.begin(), poly.end(), bound, [](auto const & term, LVRef val) {
       return term.var.x < val.x;
    });
    if (it == poly.end()) { return nullptr; }
    return it->var == bound ? &it->coeff : nullptr;
}

namespace {

struct HNFOperationsResult {
    ColMatrix operations;
    std::size_t HNFdimension;
};

ColMatrix identityMatrix(std::size_t size) {
    ColMatrix id(RowCount{size}, ColumnCount{size});
    for (std::size_t i = 0; i < size; ++i) {
        Polynomial poly;
        poly.addTerm(LVRef{static_cast<unsigned>(i)}, 1);
        id.setColumn(ColIndex{i}, std::move(poly));
    }
    return id;
}

void negateColumn(ColMatrix & A, ColIndex colIndex, ColMatrix & U) {
        A[colIndex].negate();
        U[colIndex].negate();
}

void swapColumns(ColMatrix & A, ColIndex pivotIndex, ColIndex otherIndex, ColMatrix & U) {
    assert(pivotIndex != otherIndex);
    A.swapCols(pivotIndex, otherIndex);
    U.swapCols(pivotIndex, otherIndex);
}

void addColumnMultiple(ColMatrix & A, ColIndex colFrom, opensmt::Real multiple, ColIndex colTo, ColMatrix & U) {
    A[colTo].add(A[colFrom], multiple);
    // For U we do the inverse operation: colFrom += -multiple * colTo
    U[colFrom].add(U[colTo], -multiple);
}

// normalizes row so all entries to the right of pivot are zero
// returns true if the pivot is non-zero
bool normalizeRow(ColMatrix & A, RowIndex rowIndex, ColIndex colToStart, ColMatrix & U) {
    // Collect all columns with non-zero entry at given row; ensure they are positive
    std::vector<ColIndex> activeColumns;
    auto size = A.colCount();
    activeColumns.reserve(size - colToStart);
    for (std::size_t col = colToStart; col < size; ++col) {
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
        std::size_t nextColIndex = 1;
        while(nextColIndex < activeColumns.size()) {
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
    if (activeColumns[0] != colToStart) {
        swapColumns(A, activeColumns[0], colToStart, U);
    }
    return true;
}

void reduceToTheLeft(ColMatrix & A, RowIndex rowIndex, ColIndex pivotIndex, ColMatrix & U) {
    auto const & pivotCol = A[pivotIndex];
    assert(pivotCol.isFirst(rowIndex));
    auto const & pivotVal = pivotCol.getFirstCoeff();
    for (std::size_t col = 0; col < pivotIndex; ++col) {
        auto const * otherVal = A[col].tryGetCoeffFor(rowIndex);
        if (not otherVal) { continue; }
        auto quotient = -fastrat_fdiv_q(*otherVal, pivotVal);
        if (not quotient.isZero()) {
            addColumnMultiple(A, pivotIndex, quotient, ColIndex{col}, U);
        }
    }
}

HNFOperationsResult toHNFOperations(ColMatrix && A) {
    // We perform column operations on A to transform it to HNF
    // At the same time we record the inverse operations in U
    // We maintain the invariant that A'*U' = A; starting with U=I, the identity matrix
    // We actually maintain the transpose the U as column matrix and not U as row matrix
    std::size_t cols = A.colCount();
    std::size_t rows = A.rowCount();
    ColMatrix UT = identityMatrix(cols);

    std::size_t pivotCol = 0;
    for (std::size_t currRow = 0; currRow < rows and pivotCol < cols; ++currRow) {
        // First make sure the current row conforms to the lower triangular form
        bool hasPivot = normalizeRow(A, RowIndex{currRow}, ColIndex{pivotCol}, UT);
        if (not hasPivot) {
            // a row that is linearly dependent on rows above it; skip it and continue with the next row
            // DO NOT INCREMENT PIVOT!
            continue;
        }
        // Now make sure it conforms to HNF rule that elements to the left of pivot are smaller and positive
        reduceToTheLeft(A, RowIndex{currRow}, ColIndex{pivotCol}, UT);
        // DO NOT FORGET TO INCREMENT PIVOT!
        ++pivotCol;
    }
    return {std::move(UT), pivotCol};
}
}

namespace { // Initialization
struct Representation {
    ColMatrix A;
    std::vector<FastRational> rhs;
    std::vector<PTRef> columnIndexToVarMap;
};
Representation initFromConstraints(std::vector<CutCreator::DefiningConstaint> const & constraints, ArithLogic & logic) {
    std::unordered_map<PTRef, unsigned, PTRefHash> varIndices;
    unsigned columns = 0;
    vec<PTRef> terms;
    auto fillTerms = [&](PTRef poly) {
        terms.clear();
        if (logic.isPlus(poly)) {
            for (PTRef arg : logic.getPterm(poly)) {
                terms.push(arg);
            }
        } else {
            terms.push(poly);
        }
    };
    // First pass to assign indices and find out number of columns
    for (auto defConstraint : constraints) {
        PTRef poly = defConstraint.lhs;
        fillTerms(poly);
        for (PTRef arg : terms) {
            auto [var, constant] = logic.splitTermToVarAndConst(arg);
            assert(var != PTRef_Undef);
            if (varIndices.find(var) == varIndices.end()) {
                varIndices.insert({var, columns++});
            }
        }
    }

    unsigned rows = constraints.size();
    ColMatrix matrixA(RowCount{rows}, ColumnCount{columns});
    std::vector<FastRational> rhs(RowCount{rows});
    std::vector<Polynomial> columnPolynomials;
    columnPolynomials.resize(columns);

    // Second pass to build the actual matrix
    for (unsigned row = 0; row < constraints.size(); ++row) {
        rhs[row] = constraints[row].rhs;
        PTRef poly = constraints[row].lhs;
        fillTerms(poly);
        for (PTRef arg : terms) {
            auto [var, constant] = logic.splitTermToVarAndConst(arg);
            auto col = varIndices[var];
            columnPolynomials[col].addTerm(LVRef{row}, logic.getNumConst(constant));
        }
    }
    for (std::size_t i = 0; i < columnPolynomials.size(); ++i) {
        matrixA.setColumn(ColIndex{i}, std::move(columnPolynomials[i]));
    }
    // compute the inverse map from column indices to variables
    std::vector<PTRef> columnMapping;
    columnMapping.resize(matrixA.colCount(), PTRef_Undef);
    for (auto [var, index] : varIndices) {
        columnMapping[index] = var;
    }
    return {std::move(matrixA), std::move(rhs), std::move(columnMapping)};
}
}

namespace { // check feasibility
    FastRational crossProduct(ColMatrix::Col const & col, std::vector<FastRational> const & values) {
        return col.product(values);
    }

    PTRef buildCutConstraint(ColMatrix::Col const & constraintCol, std::vector<PTRef> const & toVarMap, ArithLogic & logic) {
        return constraintCol.buildCutConstraint(toVarMap, logic);
    }
}

PTRef CutCreator::cut(std::vector<DefiningConstaint> constraints) {
    auto [matrixA, rhs, columnMapping] = initFromConstraints(constraints, logic);

    assert(matrixA.colCount() == columnMapping.size());
    std::size_t varCount = matrixA.colCount();

    auto [operations, dim] = toHNFOperations(std::move(matrixA));

    // Now examime the rows of U':=operations; multiply it with vector of current values of the variables;
    // Since we actually represented the transpose of U', each row of 'operations' corresponds to an original variable
    // and we need to remember which one
    std::vector<opensmt::Real> varValues;
    varValues.reserve(varCount);
    for (std::size_t col = 0; col < varCount; ++col) {
        PTRef var = columnMapping[col];
        varValues.push_back(evaluate(var));
    }
    // Check every row of U' for feasibility
    for (std::size_t rowIndex = 0; rowIndex < dim; ++rowIndex) {
        auto const & row = operations[rowIndex];
        auto product = crossProduct(row, varValues);
        if (not product.isInteger()) {
            PTRef constraint = buildCutConstraint(row, columnMapping, logic);
            auto lowerBoundValue = product.ceil();
            auto upperBoundValue = product.floor();
            PTRef upperBound = logic.mkLeq(constraint, logic.mkIntConst(upperBoundValue));
            PTRef lowerBound = logic.mkGeq(constraint, logic.mkIntConst(lowerBoundValue));
            return logic.mkOr(upperBound, lowerBound);
        }
    }
    return PTRef_Undef;
}

