/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */


#include "CutCreator.h"

namespace{
    void negate(std::vector<opensmt::Real> & elements) {
        for (auto & val : elements) {
            if (not val.isZero()) {
                val.negate();
            }
        }
    }

    void add(std::vector<opensmt::Real> & res, std::vector<opensmt::Real> const & what, opensmt::Real const & multiple) {
        assert(res.size() == what.size());
        for (std::size_t i = 0; i < what.size(); ++i) {
            if (what[i].isZero()) { continue; }
            res[i] += what[i] * multiple;
        }
    }
}

void Row::negate() {
    ::negate(this->elements);
}

void Column::negate() {
    ::negate(this->elements);
}

void Row::add(const Row & other, opensmt::Real const & multiple) {
    ::add(this->elements, other.elements, multiple);
}

void Column::add(const Column & other, opensmt::Real const & multiple) {
    ::add(this->elements, other.elements, multiple);
}

namespace {

struct HNFOperationsResult {
    RowMatrix operations;
    std::size_t HNFdimension;
};

RowMatrix rowIdentityMatrix(std::size_t size) {
    RowMatrix id(RowCount{size}, ColumnCount{size});
    for (std::size_t i = 0; i < size; ++i) {
        id[i][i] = 1;
    }
    return id;
}

std::size_t findSmallestNonzeroElementInRow(ColMatrix const & A, RowIndex rowIndex, ColIndex colToStart) {
    auto size = A.colCount();
    // find first non-zero element
    std::size_t smallestNonZeroIndex;
    for (smallestNonZeroIndex = colToStart; smallestNonZeroIndex < size; ++smallestNonZeroIndex) {
        if (not A[smallestNonZeroIndex][rowIndex].isZero()) {
            break;
        }
    }
    if (smallestNonZeroIndex == size) {
        return smallestNonZeroIndex;
    }
    auto smallestVal = A[smallestNonZeroIndex][rowIndex];
    // find smallest element (in absolute value)
    for (std::size_t col = smallestNonZeroIndex + 1; col < size; ++col) {
        auto const & val = A[col][rowIndex];
        if (not val.isZero() and cmpabs(val, smallestVal) < 0) {
            smallestVal = val;
            smallestNonZeroIndex = col;
        }
    }
    return smallestNonZeroIndex;
}

void swapColumns(ColMatrix & A, ColIndex pivotIndex, ColIndex otherIndex, RowMatrix & U) {
    assert(pivotIndex != otherIndex);
    std::swap(A[pivotIndex], A[otherIndex]);
    std::swap(U[pivotIndex], U[otherIndex]);
}

void ensurePositivePivot(ColMatrix & A, RowIndex rowIndex, ColIndex pivotIndex, RowMatrix & U) {
    auto & val = A[pivotIndex][rowIndex];
    assert(not val.isZero());
    if (val.sign() < 0) {
        A[pivotIndex].negate();
        U[pivotIndex].negate();
    }
}

void addColumnMultiple(ColMatrix & A, std::size_t colFrom, opensmt::Real multiple, std::size_t colTo, RowMatrix & U) {
    A[colTo].add(A[colFrom], multiple);
    // For U we do the inverse operation: colFrom += -multiple * colTo
    U[colFrom].add(U[colTo], -multiple);
}

void reduceToTheRight(ColMatrix & A, RowIndex rowIndex, ColIndex pivotIndex, RowMatrix & U) {
    auto pivotVal = A[pivotIndex][rowIndex];
    auto size = A.colCount();
    for (std::size_t col = pivotIndex + 1; col < size; ++col) {
        auto otherVal = A[col][rowIndex];
        if (otherVal.isZero()) { continue; }
        auto quotient = -fastrat_fdiv_q(otherVal, pivotVal);
        assert(not quotient.isZero());
        addColumnMultiple(A, pivotIndex, quotient, col, U);
    }
}

void reduceToTheLeft(ColMatrix & A, RowIndex rowIndex, ColIndex pivotIndex, RowMatrix & U) {
    auto pivotVal = A[pivotIndex][rowIndex];
    for (std::size_t col = 0; col < pivotIndex; ++col) {
        auto otherVal = A[col][rowIndex];
        if (otherVal.isZero()) { continue; }
        auto quotient = -fastrat_fdiv_q(otherVal, pivotVal);
        if (not quotient.isZero()) {
            addColumnMultiple(A, pivotIndex, quotient, col, U);
        }
    }
}

HNFOperationsResult toHNFOperations(ColMatrix && A) {
    // We perform column operations on A to transform it to HNF
    // At the same time we record the inverse operations in U
    // We maintain the invariant that A'*U' = A; starting with U=I, the identity matrix
    std::size_t cols = A.colCount();
    std::size_t rows = A.rowCount();
    RowMatrix U = rowIdentityMatrix(cols);

    std::size_t pivotCol = 0;
    for (std::size_t currRow = 0; currRow < rows and pivotCol < cols; ++currRow) {
        // First make sure the current row conforms to the lower triangular form
        while (true) {
            auto colIndex = findSmallestNonzeroElementInRow(A, RowIndex{currRow}, ColIndex{pivotCol + 1});
            if (colIndex == cols) { break; }
            if (A[pivotCol][currRow].isZero() or cmpabs(A[colIndex][currRow], A[pivotCol][currRow]) < 0) {
                swapColumns(A, ColIndex{pivotCol}, ColIndex{colIndex}, U);
            }
            ensurePositivePivot(A, RowIndex{currRow}, ColIndex{pivotCol}, U);
            reduceToTheRight(A, RowIndex{currRow}, ColIndex{pivotCol}, U);
        }
        if (A[pivotCol][currRow].isZero()) {
            // a row that is linearly dependent on rows above it; skip it and continue with the next row
            // DO NOT INCREMENT PIVOT!
            continue;
        }
        // Now make sure it conforms to HNF rule that elements to the left of pivot are smaller and positive
        reduceToTheLeft(A, RowIndex{currRow}, ColIndex{pivotCol}, U);
        // DO NOT FORGET TO INCREMENT PIVOT!
        ++pivotCol;
    }
    return {U, pivotCol};
}
}

namespace { // Initialization
struct Representation {
    ColMatrix A;
    Column rhs;
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
    ColMatrix matrixA(ColumnCount{columns}, RowCount{rows});
    Column rhs(RowCount{rows});

    // Second pass to build the actual matrix
    for (unsigned row = 0; row < constraints.size(); ++row) {
        rhs[row] = constraints[row].rhs;
        PTRef poly = constraints[row].lhs;
        fillTerms(poly);
        for (PTRef arg : terms) {
            auto [var, constant] = logic.splitTermToVarAndConst(arg);
            auto col = varIndices[var];
            matrixA[col][row] = logic.getNumConst(constant);
        }
    }
    // compute the inverse map from column indices to variables
    std::vector<PTRef> columnMapping;
    columnMapping.resize(matrixA.colCount(), PTRef_Undef);
    for (auto [var, index] : varIndices) {
        columnMapping[index] = var;
    }
    return {matrixA, rhs, columnMapping};
}
}

namespace { // check feasibility
    FastRational crossProduct(Row const & row, std::vector<FastRational> const & values) {
        assert(row.size() == values.size());
        FastRational sum = 0;
        for (std::size_t i = 0; i < values.size(); ++i) {
            sum += row[i] * values[i];
        }
        return sum;
    }

    PTRef buildCutConstraint(Row const & row, std::vector<PTRef> const & colMapping, ArithLogic & logic) {
        assert(row.size() == colMapping.size());
        vec<PTRef> args; args.capacity(row.size());
        for (std::size_t col = 0; col < row.size(); ++col) {
            if (row[col].isZero()) { continue; }
            args.push(logic.mkTimes(colMapping[col], logic.mkIntConst(row[col])));
        }
        return logic.mkPlus(std::move(args));
    }
}

PTRef CutCreator::cut(std::vector<DefiningConstaint> constraints) {
    auto [matrixA, rhs, columnMapping] = initFromConstraints(constraints, logic);

    assert(matrixA.colCount() == columnMapping.size());
    std::size_t varCount = matrixA.colCount();

    auto [operations, dim] = toHNFOperations(std::move(matrixA));

    // Now examime the rows of U':=operations; multiple it with vector of current values of the variables;
    // Note that each column of U' corresponds to an original variable and we need to remember which one
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

