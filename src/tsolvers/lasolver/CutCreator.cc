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
        uint32_t index = term.var.x;
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
ColMatrix identityMatrix(uint32_t size) {
    ColMatrix id(RowCount{size}, ColumnCount{size});
    for (uint32_t i = 0; i < size; ++i) {
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

void addColumnMultiple(ColMatrix & A, ColIndex colFrom, opensmt::Real const & multiple, ColIndex colTo, ColMatrix & U) {
    A[colTo].add(A[colFrom], multiple);
    // For U we do the inverse operation: colFrom += -multiple * colTo
    U[colFrom].add(U[colTo], -multiple);
}

/*
 * Normalizes row so that all entries to the right of pivot are zero.
 * Returns true if the pivot is non-zero.
 */
bool normalizeRow(ColMatrix & A, RowIndex rowIndex, ColIndex pivotIndex, ColMatrix & U) {
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

void reduceToTheLeft(ColMatrix & A, RowIndex rowIndex, ColIndex pivotIndex, ColMatrix & U) {
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

struct HNFOperationsResult {
    ColMatrix operations;
    uint32_t HNFdimension;
};

HNFOperationsResult toHNFOperations(ColMatrix && A) {
    // We perform column operations on A to transform it to HNF
    // At the same time we record the inverse operations in U
    // We maintain the invariant that A'*U' = A; starting with U:=I, the identity matrix
    // We actually maintain the transpose of U' as column matrix and not U' as row matrix
    uint32_t cols = A.colCount();
    uint32_t rows = A.rowCount();
    ColMatrix UT = identityMatrix(cols);

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
/*
 * Translates the set of defining constraints (linear equalities) into a suitable inner representation:
 * - Matrix A of coefficients
 * - a vector with right-hand-side values (as Rationals)
 * - a map from column index to the corresponding variable
 */
Representation initFromConstraints(std::vector<CutCreator::DefiningConstaint> const & constraints, ArithLogic & logic) {
    vec<PTRef> terms;
    auto fillTerms = [&](PTRef poly) {// reduces linear polynomial to a vector of the polynomial's terms
        terms.clear();
        if (logic.isPlus(poly)) {
            for (PTRef arg : logic.getPterm(poly)) {
                terms.push(arg);
            }
        } else {
            terms.push(poly);
        }
    };
    std::unordered_map<PTRef, unsigned, PTRefHash> varIndices;
    uint32_t columns = 0;
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

    auto rows = static_cast<uint32_t>(constraints.size());
    ColMatrix matrixA(RowCount{rows}, ColumnCount{columns});
    std::vector<FastRational> rhs(rows);
    std::vector<Polynomial> columnPolynomials(columns);

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
    for (uint32_t i = 0; i < columnPolynomials.size(); ++i) {
        matrixA.setColumn(ColIndex{i}, std::move(columnPolynomials[i]));
    }
    // compute the inverse map from column indices to variables
    std::vector<PTRef> columnMapping(matrixA.colCount(), PTRef_Undef);
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

    PTRef infeasibleRowToCut(ColMatrix::Col const & constraintCol, std::vector<PTRef> const & toVarMap, ArithLogic & logic,
                             FastRational const & rhs) {
        PTRef constraint = constraintCol.buildCutConstraint(toVarMap, logic);
        auto lowerBoundValue = rhs.ceil();
        auto upperBoundValue = rhs.floor();
        PTRef upperBound = logic.mkLeq(constraint, logic.mkIntConst(upperBoundValue));
        PTRef lowerBound = logic.mkGeq(constraint, logic.mkIntConst(lowerBoundValue));
        return logic.mkOr(upperBound, lowerBound);
    }
}

PTRef CutCreator::cut(std::vector<DefiningConstaint> const & constraints) {
    auto [matrixA, rhs, columnMapping] = initFromConstraints(constraints, logic);
    // MB: 'rhs' is not really used, as it is implicit in the variable assignment; maybe we don't have to compute it

    assert(matrixA.colCount() == columnMapping.size());
    uint32_t varCount = matrixA.colCount();

    auto [matrixU, dim] = toHNFOperations(std::move(matrixA));

    // Get the values of the variables
    std::vector<opensmt::Real> varValues;
    varValues.reserve(varCount);
    for (uint32_t col = 0; col < varCount; ++col) {
        PTRef var = columnMapping[col];
        varValues.push_back(evaluate(var));
    }
    // Now check every row of U for infeasibility: if the cross product of the row and vector of variable values is not
    // an integer, the row represents an infeasible constraint
    for (uint32_t rowIndex = 0; rowIndex < dim; ++rowIndex) {
        auto const & row = matrixU[rowIndex];
        auto product = crossProduct(row, varValues);
        if (not product.isInteger()) {
            return infeasibleRowToCut(row, columnMapping, logic, product);
        }
    }
    return PTRef_Undef;
}

