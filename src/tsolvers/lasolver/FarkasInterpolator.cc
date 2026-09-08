/*
 *  Copyright (c) 2018-2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

// #ifndef NDEBUG
// #define TRACE
// #endif

#ifdef TRACE
#define trace(x) x
#else
#define trace(x)
#endif

#include "FarkasInterpolator.h"

#include <common/ApiException.h>
#include <common/InternalException.h>
#include <common/numbers/Real.h>
#include <common/polynomials/Translations.h>
#include <logics/ArithLogic.h>
#include <rewriters/Rewritings.h>

#include <functional>
#include <unordered_map>

namespace opensmt {
using matrix_t = std::vector<std::vector<Real>>;

// initializing static member
DecomposedStatistics FarkasInterpolator::stats{};

enum class Strictness { NONSTRICT, STRICT };

/// The paper's `LA(s <| 0, k)`: a linear combination `s` over shared variables (and, transiently,
/// fresh mixed auxiliary variables), together with the parameter `k`.
///
/// For LRA, `k` only needs to record strictness. Steps 2-3 (LIA) additionally use it to carry the
/// integer scaling / cut divisor with which the mixed auxiliary variable entered, and to emit
/// divisibility atoms when that variable is eliminated. In this step `k` is always 0 and the
/// auxiliary variables are left untouched in `s`, so the produced interpolant is unchanged.
struct LATerm {
    LAPoly s;
    Strictness strictness = Strictness::NONSTRICT;
    Real k = 0;
    std::vector<PTRef> auxVars; // fresh `.mixed_*` variables still present in `s`
    SRef sort = SRef_Undef;
};

/// Result of splitting a mixed (A/B) inequality literal into an A-colorable and a B-colorable half,
/// kept as polynomials (not lowered to PTRef) so that later steps can reason about the shared
/// auxiliary variable and the coefficient with which it enters.
struct MixedSplit {
    LAPoly aPart;               // A-colorable:  0 <= aPart   (contains auxVar with coeff -1)
    LAPoly bPart;               // B-colorable:  0 <= bPart   (contains auxVar with coeff +1, plus const)
    PTRef auxVar = PTRef_Undef; // fresh shared var connecting the halves; PTRef_Undef if the split was trivial
    Real auxCoeff = 1;          // coeff the aux var entered with: 1 for LRA, the cut divisor for LIA (step 2)
    SRef sort = SRef_Undef;
    bool trivial = false;
};

/// Given a polynomial @p poly, returns an inequality equivalent to "0 <= poly" (or <= 0, depending on @p strictness)
PTRef toInequality(LAPoly poly, ArithLogic & logic, SRef const type, Strictness const strictness) {
    if (poly.size() == 0) { return strictness == Strictness::NONSTRICT ? logic.getTerm_true() : logic.getTerm_false(); }
    PTRef const sum = polyToPTRef(poly, logic, type);
    PTRef const zero = logic.getZeroForSort(type);
    return strictness == Strictness::NONSTRICT ? logic.mkGeq(sum, zero) : logic.mkGt(sum, zero);
}

namespace {
    // TODO: when is explanation negated?
    struct ItpHelper {
        ItpHelper(ArithLogic & logic, PtAsgn ineq, Real coeff)
            : explanation(ineq.tr),
              negated(ineq.sgn == l_False),
              expl_coeff(std::move(coeff)),
              poly(ptrefToPoly(ineq.tr, logic)) {}
        PTRef explanation;
        bool negated;
        Real expl_coeff;
        LAPoly poly;
    };

    struct LinearTerm {
        LinearTerm(PTRef var_, Real coeff_) : var(var_), coeff(std::move(coeff_)) {}
        PTRef var;
        Real coeff;
    };

    using Basis = std::vector<std::vector<Real>>;
    using Coordinates = std::vector<Real>;

    std::vector<LinearTerm> getLocalTerms(ItpHelper const & helper, std::function<bool(PTRef)> isLocal) {
        std::vector<LinearTerm> res;
        for (auto const & [var, coeff] : helper.poly) {
            if (var != PTRef_Undef) {
                if (isLocal(var)) { res.emplace_back(var, helper.negated ? -coeff : coeff); }
            }
        }
        return res;
    }

    /**
     *
     * @param matrix
     * @param pivotCol
     * @param startRow
     * @return Index of row >= startRow that contains the pivot for given column pivotCol
     */
    std::size_t getPivotRow(matrix_t const & matrix, std::size_t pivotCol, std::size_t startRow) {
        for (auto i = startRow; i < matrix.size(); ++i) {
            if (matrix[i][pivotCol] != 0) { return i; }
        }
        return matrix.size();
    }

    /** Adds a multiple of vector of Reals to another vector with equal size.
     *
     * @param to vector to which we add
     * @param what vector being added
     * @param coeff The multiple
     */
    void addToWithCoeff(std::vector<Real> & to, std::vector<Real> const & what, Real const & coeff) {
        assert(to.size() == what.size());
        for (std::size_t i = 0; i < what.size(); ++i) {
            to[i] += coeff * what[i];
        }
    }

    // assumes there are 0 on all position before col
    void normalize(std::vector<Real> & row, std::size_t col) {
#ifndef NDEBUG
        for (std::size_t i = 0; i < col; ++i) {
            assert(row[i] == 0);
        }
#endif // NDEBUG
        auto val = row[col].inverse();
        for (; col < row.size(); ++col) {
            row[col] *= val;
        }
    }

    /** Transforms a matrix in a Row Echolon Form to matrix in Reduced Row Echolob Form
     *
     * @param matrix Matrix in REF
     */
    void toReducedRowEcholonForm(std::vector<std::vector<Real>> & matrix) {
        std::vector<std::size_t> pivotColInds;
        std::size_t column = 0;
        for (auto & row : matrix) {
            auto it = std::find_if(row.begin() + column, row.end(), [](Real const & el) { return !el.isZero(); });
            if (it == row.end()) { continue; }
            column = it - row.begin();
            assert(pivotColInds.empty() || pivotColInds.back() < column);
            pivotColInds.push_back(column);
            if (row[column] != 1) { normalize(row, column); }
        }

        // TODO: use long instead of int?
        for (auto rowInd = (int)(matrix.size() - 1); rowInd >= 0; --rowInd) {
            auto & row = matrix[rowInd];
            auto pivotColInd = pivotColInds.back();
            if (row[pivotColInd].isZero()) { continue; }
            pivotColInds.pop_back();
            assert(row[pivotColInd] == 1);
            for (int rowInd2 = rowInd - 1; rowInd2 >= 0; --rowInd2) {
                if (matrix[rowInd2][pivotColInd].isZero()) { continue; }
                addToWithCoeff(matrix[rowInd2], row, -matrix[rowInd2][pivotColInd]);
            }
        }
    }

    /** Transforms a matrix to Row Echolon Form
     *
     * @param matrix
     */
    void gaussianElimination(matrix_t & matrix) {
        std::size_t cols = matrix[0].size();
        std::size_t pivotRow = 0;
        std::size_t pivotCol = 0;
        while (pivotCol < cols && pivotRow < matrix.size()) {
            // find the row with non-zero coefficient
            auto nextRow = getPivotRow(matrix, pivotCol, pivotRow);
            if (nextRow == matrix.size()) {
                // all remaining rows have 0 in this column -> continue with next column
                ++pivotCol;
                continue;
            }
            // put it to correct place
            if (nextRow != pivotRow) { std::swap(matrix[pivotRow], matrix[nextRow]); }
            // now zero out the column after the current row
            for (auto row = pivotRow + 1; row < matrix.size(); ++row) {
                if (matrix[row][pivotCol] == 0) { continue; }
                addToWithCoeff(matrix[row], matrix[pivotRow], -(matrix[row][pivotCol] / matrix[pivotRow][pivotCol]));
#ifndef NDEBUG
                for (std::size_t col = 0; col <= pivotCol; ++col) {
                    assert(matrix[row][col] == 0);
                }
#endif // NDEBUG
            }
            ++pivotRow;
            ++pivotCol;
        }
    }

    /*
     * Returns nullity (dimension of the null space) of given matrix
     */
    std::size_t getNullity(std::vector<std::vector<Real>> const & matrix) {
        // nullity is the number of columns - rank
        auto rank = std::count_if(matrix.cbegin(), matrix.cend(), [](std::vector<Real> const & row) {
            return std::any_of(row.cbegin(), row.cend(), [](Real const & r) { return r != 0; });
        });
        auto cols = static_cast<long>(matrix[0].size());
        assert(cols >= rank);
        return cols - rank;
    }

    /*
     * Given matrix in REF, return bitmap of columns with pivot columns identified
     */
    std::vector<bool> getPivotColsBitMap(std::vector<std::vector<Real>> const & matrix) {
        std::vector<bool> pivotColsBitMap;
        auto cols = matrix[0].size();
        pivotColsBitMap.resize(cols);
        std::size_t row = 0;
        for (std::size_t col = 0; col < cols; ++col) {
            // check if this column is a pivot column
            // if we are out of rows it is not a pivot
            if (row == matrix.size() || matrix[row][col].isZero()) {
                pivotColsBitMap[col] = false;
            } else {
                assert(matrix[row][col] == 1);
                pivotColsBitMap[col] = true;
                ++row;
            }
        }
        return pivotColsBitMap;
    }

#ifndef NDEBUG // ======== DEBUG METHODS ================
    bool isReducedRowEchelonForm(std::vector<std::vector<Real>> const & matrix) {
        auto pivotColsBitMap = getPivotColsBitMap(matrix);
        auto cols = pivotColsBitMap.size();
        assert(cols == matrix[0].size());
        std::size_t pivotRow = 0;
        for (unsigned int col = 0; col < pivotColsBitMap.size(); ++col) {
            if (pivotColsBitMap[col]) {
                for (std::size_t row = 0; row < matrix.size(); ++row) {
                    if ((row != pivotRow && matrix[row][col] != 0) || (row == pivotRow && matrix[row][col] != 1)) {
                        return false;
                    }
                }
                ++pivotRow;
            } else { // free column (not pivot)
                for (auto row = pivotRow; row < matrix.size(); ++row) {
                    if (matrix[row][col] != 0) { return false; }
                }
            }
        }
        return true;
    }

    bool check_basis(std::vector<std::vector<Real>> const & basis) {
        return std::all_of(basis.begin(), basis.end(), [](std::vector<Real> const & baseVec) {
            return std::none_of(baseVec.begin(), baseVec.end(), [](Real const & el) { return el < 0; });
        });
    }

#ifdef TRACE
    void print_matrix(std::vector<std::vector<Real>> const & matrix) {
        (void)print_matrix; // MB: to supress compiler warning for this unused helpful debug method
        for (auto const & row : matrix) {
            for (auto const & elem : row) {
                std::cout << elem << " ";
            }
            std::cout << '\n';
        }
        std::cout << '\n';
    }

    void print_basis(std::vector<std::vector<Real>> const & nullBasis) {
        (void)print_basis; // MB: to supress compiler warning for this unused helpful debug method
        std::cout << "Basis: " << '\n';
        for (auto const & base : nullBasis) {
            for (auto const & elem : base) {
                std::cout << elem << ' ';
            }
            std::cout << '\n';
        }
        std::cout << '\n';
    }

#endif // TRACE

    bool isDecomposition(Basis const & basis, Coordinates const & coordinates, std::vector<Real> const & original) {
        assert(coordinates.size() == basis.size());
        assert(std::all_of(basis.begin(), basis.end(), [&original](std::vector<Real> const & baseVec) {
            return baseVec.size() == original.size();
        }));
        for (std::size_t i = 0; i < original.size(); ++i) {
            Real sum = 0;
            for (std::size_t j = 0; j < basis.size(); ++j) {
                sum += basis[j][i] * coordinates[j];
            }
            if (sum != original[i]) { return false; }
        }
        return true;
    }

#endif // NDEBUG // ======== DEBUG METHODS ================

    /** Given matrix in RREF computes and returns a basis of its null space
     *
     * @see https://en.wikibooks.org/wiki/Linear_Algebra/Null_Spaces
     * @param matrix in RREF
     * @return Basis of null space of given matrix
     */
    std::vector<std::vector<Real>> getNullBasis(std::vector<std::vector<Real>> const & matrix) {
        assert(isReducedRowEchelonForm(matrix));
        std::vector<std::vector<Real>> basis;
        auto pivotColsBitMap = getPivotColsBitMap(matrix);
        auto cols = matrix[0].size();
        assert(cols == pivotColsBitMap.size());
        // for non-pivot columns generate a new base vector
        for (std::size_t col = 0; col < cols; ++col) {
            if (pivotColsBitMap[col]) { continue; }
            basis.emplace_back();
            auto & base_vector = basis.back();

            // put 1 on position of this free column, 0 on positions of other free columns, and -val at pivot row
            unsigned int pivotRow = 0;
            for (unsigned int colPos = 0; colPos < cols; ++colPos) {
                if (pivotColsBitMap[colPos]) {
                    base_vector.push_back(-matrix[pivotRow][col]);
                    ++pivotRow;
                } else { // free column
                    base_vector.push_back(colPos == col ? 1 : 0);
                }
            }
        }
        return basis;
    }

    PTRef sumInequalities(std::vector<ItpHelper> const & ineqs, std::vector<Real> const & coeffs, ArithLogic & logic) {
        assert(ineqs.size() == coeffs.size());
        assert(ineqs.size() > 0);
        LAPoly poly;
        auto it_ineq = ineqs.begin();
        auto it_coeff = coeffs.begin();
        Strictness strictness = Strictness::NONSTRICT;
        SRef itpSort = logic.getSortRef(logic.getPterm(ineqs[0].explanation)[0]);
        for (; it_ineq != ineqs.end(); ++it_ineq, ++it_coeff) {
            auto const & coeff = *it_coeff;
            if (coeff.isZero()) { continue; } // when some basis is found, some coordinates could be zero; ignore those
            auto const & ineq = *it_ineq;
            trace(std::cout << "Original explanation: " << logic.termToSMT2String(ineq.explanation)
                            << "; negated: " << ineq.negated << '\n');
            trace(std::cout << "LAExpr as PTrEf: " << logic.termToSMT2String(ineq.expr.toPTRef()) << '\n');
            trace(std::cout << "LAExpr as stored: ");
            trace(ineq.expr.print(std::cout); std::cout << std::endl);
            if (ineq.negated) {
                strictness = Strictness::STRICT;
                poly.merge(ineq.poly, -coeff);
            } else {
                poly.merge(ineq.poly, coeff);
            }
            trace(init.print(std::cout));
        }
        return toInequality(std::move(poly), logic, itpSort, strictness);
    }

    PTRef sumInequalities(std::vector<ItpHelper> const & ineqs, ArithLogic & logic) {
        std::vector<Real> coeffs;
        coeffs.reserve(ineqs.size());
        for (auto const & helper : ineqs) {
            coeffs.push_back(helper.expl_coeff);
        }
        return sumInequalities(ineqs, coeffs, logic);
    }

    std::vector<Real> getFarkasCoeffs(std::vector<ItpHelper> const & inequalities) {
        std::vector<Real> ret;
        for (auto const & ineq : inequalities) {
            ret.push_back(ineq.expl_coeff);
        }
        return ret;
    }

    // Gets coordinates (alphas) with respect to current basis. Relies on the fact that
    // explanations_with_locals and columns of matrix are in 1-1 correspondence (including ordering)
    // Moreover, it relies on how the basis is computed, namely that for a given free (non-pivot) column
    // and its corresponding position, there is exactly one vector in basis with 1 in that position and all
    // other vectors in basis have 0 in that position. Consequently, the coordinate for that vector is the element
    // in Farkas coefficients at that position
    template<typename T>
    std::vector<Real> getAlphas(std::vector<Real> const & allFarkasCoeffs, T & isPivot) {
        std::vector<Real> ret;
        for (std::size_t i = 0; i < allFarkasCoeffs.size(); ++i) {
            if (!isPivot(i)) { ret.push_back(allFarkasCoeffs[i]); }
        }
        return ret;
    }

    void ensureNonNegativeVec(std::vector<Real> & baseVec, std::size_t baseVecIndex, Coordinates & coordinates,
                              std::vector<Real> const & vecToDecompose) {
        for (std::size_t i = 0; i < baseVec.size(); ++i) {
            if (baseVec[i] < 0) {
                auto coeff = (-baseVec[i] / vecToDecompose[i]);
                // baseVec += coeff * vecToDecompose;
                for (std::size_t j = 0; j < baseVec.size(); ++j) {
                    baseVec[j] += coeff * vecToDecompose[j];
                }
                // update coordinates
                Real divisor = Real{1} + (coeff * coordinates[baseVecIndex]);
                for (Real & coordinate : coordinates) {
                    coordinate /= divisor;
                }
            }
        }
    }

    void ensureNonNegativeDecomposition(Basis & basis, Coordinates & coordinates,
                                        std::vector<Real> const & vecToDecompose) {
        for (std::size_t i = 0; i < basis.size(); ++i) {
            ensureNonNegativeVec(basis[i], i, coordinates, vecToDecompose);
        }
    }

    struct StatsHelper {
        bool standAloneIneq = false;
        bool nonTrivialBasis = false;
        bool moreThanOneInequality = false;
    };

} // namespace

PTRef FarkasInterpolator::getDecomposedInterpolant(icolor_t color) {
    assert(color == icolor_t::I_A || color == icolor_t::I_B);
    bool hasColors = ensureHasColorForAllTerms();
    if (not hasColors) {
        throw InternalException(
            "Error in computation of decomposed Farkas interpolant, colors could not be determined!");
    }
    StatsHelper statsHelper;
    // this will be contain the result, inequalities corresponding to summed up partitions of explanataions (of
    // given color)
    std::vector<PTRef> interpolant_inequalities;
    std::vector<std::pair<PtAsgn, Real>> candidates;
    assert(explanations.size() == static_cast<int>(explanation_coeffs.size()));
    for (int i = 0; i < explanations.size(); ++i) {
        assert(explanation_coeffs[i] > 0);
        candidates.emplace_back(explanations[i], explanation_coeffs[i]);
        trace(std::cout << "Explanation " << logic.termToSMT2String(explanations[i].tr) << " with coeff "
                        << explanation_coeffs[i] << " is negated: " << (explanations[i].sgn == l_False) << '\n');
        bool isA = this->isInPartitionOfColor(icolor_t::I_A, explanations[i].tr);
        bool isB = this->isInPartitionOfColor(icolor_t::I_B, explanations[i].tr);
        if (isA) { trace(std::cout << "This explanation is from A\n"); }
        if (isB) { trace(std::cout << "This explanation is from B\n"); }
    }
    auto it = std::partition(candidates.begin(), candidates.end(), [color, this](std::pair<PtAsgn, Real> const & expl) {
        return this->isInPartitionOfColor(color, expl.first.tr);
    });
    if (it == candidates.end() || it == candidates.begin()) {
        // all inequalities are of the same color -> trivial interpolant
        // return false for all of color A and true for all of color B
        return ((it == candidates.end() && color == icolor_t::I_A) ||
                (it == candidates.begin() && color == icolor_t::I_B))
                 ? logic.getTerm_false()
                 : logic.getTerm_true();
    }
    std::vector<ItpHelper> helpers;
    ArithLogic & logic = this->logic;
    std::transform(candidates.begin(), it, std::back_inserter(helpers), [&logic](std::pair<PtAsgn, Real> const & expl) {
        return ItpHelper{logic, expl.first, expl.second};
    });
    statsHelper.moreThanOneInequality = helpers.size() > 1;
    using local_terms_t = std::vector<LinearTerm>;
    // create information about local variables for each inequality
    std::vector<local_terms_t> ineqs_local_vars;
    std::vector<ItpHelper> explanations_with_locals;
    for (auto const & helper : helpers) {
        local_terms_t local_terms =
            getLocalTerms(helper, [this, color](PTRef ptr) { return this->isLocalFor(color, ptr); });

        // explanataion with all variables shared form standalone partition
        if (local_terms.empty()) {
            statsHelper.standAloneIneq = true;
            interpolant_inequalities.push_back(helper.negated ? logic.mkNot(helper.explanation) : helper.explanation);
        }
        // for explanations with local variables, remember them separately
        else {
            ineqs_local_vars.push_back(std::move(local_terms));
            explanations_with_locals.push_back(helper);
        }
    }

    if (!ineqs_local_vars.empty()) {
        // assign index to each local var
        std::unordered_map<PTRef, std::size_t, PTRefHash> local_vars;
        for (auto const & info : ineqs_local_vars) {
            for (auto const & term : info) {
                if (local_vars.find(term.var) == local_vars.end()) {
                    auto size = local_vars.size();
                    local_vars[term.var] = size;
                }
            }
        }
        // create a matrix from those containing local variables
        // rows correspond to local variables, columns correspond to explanations (inequalities)

        matrix_t matrix{local_vars.size()};
        std::size_t colInd = 0;
        for (auto const & info : ineqs_local_vars) {
            // add coefficient to those rows whose corresponding variable occurs in the inequality
            for (auto const & term : info) {
                auto var = term.var;
                auto ind = local_vars[var];
                matrix[ind].push_back(term.coeff);
            }
            // add 0 to other rows
            for (auto & row : matrix) {
                if (row.size() <= colInd) {
                    assert(row.size() == colInd);
                    // push coefficient 0
                    row.emplace_back(0);
                }
            }
            ++colInd;
        }
        trace(print_matrix(matrix));
        gaussianElimination(matrix);
        trace(print_matrix(matrix));
        auto nullity = getNullity(matrix);
        // if the space of solutions does not have at least two vector in basis, we cannot do anything
        if (nullity <= 1) {
            //            std::cout << "Nullity space has single-vector basis" << '\n';
            interpolant_inequalities.push_back(sumInequalities(explanations_with_locals, logic));
        } else {
            toReducedRowEcholonForm(matrix);
            trace(print_matrix(matrix));
            auto nullBasis = getNullBasis(matrix);
            trace(print_basis(nullBasis));
            assert(explanations_with_locals.size() == matrix[0].size());
            auto farkasCoeffs = getFarkasCoeffs(explanations_with_locals);
            auto const pivotColIndexBitMap = getPivotColsBitMap(matrix);
            assert(farkasCoeffs.size() == pivotColIndexBitMap.size());
            auto isPivotColIndex = [&pivotColIndexBitMap](std::size_t index) { return pivotColIndexBitMap[index]; };
            auto alphas = getAlphas(farkasCoeffs, isPivotColIndex);
            assert(std::all_of(alphas.begin(), alphas.end(), [](Real const & v) { return v > 0; }));
            assert(alphas.size() == nullBasis.size());
            assert(isDecomposition(nullBasis, alphas, farkasCoeffs));
            ensureNonNegativeDecomposition(nullBasis, alphas, farkasCoeffs);
            assert(std::all_of(alphas.begin(), alphas.end(), [](Real const & v) { return v > 0; }));
            assert(check_basis(nullBasis));
            assert(isDecomposition(nullBasis, alphas, farkasCoeffs));
            statsHelper.nonTrivialBasis = true;
            // foreach vector in the basis, cycle over the inequalities and sum it all up, with corresponding
            // coefficient
            for (auto const & base : nullBasis) {
                interpolant_inequalities.push_back(sumInequalities(explanations_with_locals, base, logic));
            }
        }
    } else {
        assert(explanations_with_locals.empty());
    }

    if (!interpolant_inequalities.empty()) {
        if (statsHelper.moreThanOneInequality) { FarkasInterpolator::stats.decompositionOpportunities++; }
        if (interpolant_inequalities.size() > 1) {
            FarkasInterpolator::stats.decomposedItps++;
            assert(statsHelper.nonTrivialBasis || statsHelper.standAloneIneq);
            if (statsHelper.nonTrivialBasis) { FarkasInterpolator::stats.nonTrivialBasis++; }
            if (statsHelper.standAloneIneq) { FarkasInterpolator::stats.standAloneIneq++; }
        }
    }

    vec<PTRef> args;
    for (auto const & itp : interpolant_inequalities) {
        args.push(itp);
    }
    PTRef itp = logic.mkAnd(args);
    if (color == icolor_t::I_B) { itp = logic.mkNot(itp); }
    return itp;
}

icolor_t FarkasInterpolator::getGlobalColorFor(PTRef term) const {
    assert(termColorInfo);
    return termColorInfo->getColorFor(term);
}

PTRef FarkasInterpolator::getDecomposedInterpolant() {
    return getDecomposedInterpolant(icolor_t::I_A);
}

PTRef FarkasInterpolator::getDualDecomposedInterpolant() {
    return getDecomposedInterpolant(icolor_t::I_B);
}

PTRef FarkasInterpolator::getFarkasInterpolant() {
    return getFarkasInterpolant(icolor_t::I_A);
}

PTRef FarkasInterpolator::getDualFarkasInterpolant() {
    return getFarkasInterpolant(icolor_t::I_B);
}

PTRef FarkasInterpolator::weightedSum(std::vector<std::pair<PtAsgn, Real>> const & system) {
    if (system.empty()) { return logic.getTerm_true(); }
    LAPoly interpolant;
    Strictness strictness = Strictness::NONSTRICT;
    SRef sumSort = SRef_Undef;
    for (auto const & entry : system) {
        auto literal = entry.first;
        PTRef atom = literal.tr;
        sumSort = sumSort != SRef_Undef ? sumSort : logic.getUniqueArgSort(atom);
        assert(sumSort != SRef_Undef);
        lbool sign = literal.sgn;
        if (sign == l_False) {
            interpolant.merge(ptrefToPoly(atom, logic), -entry.second);
            strictness = Strictness::STRICT;
        } else {
            interpolant.merge(ptrefToPoly(atom, logic), entry.second);
        }
    }
    assert(sumSort != SRef_Undef);
    PTRef const itp = toInequality(std::move(interpolant), logic, sumSort, strictness);
    return itp;
}

PTRef FarkasInterpolator::weightedSum(std::vector<LATerm> const & system) {
    if (system.empty()) { return logic.getTerm_true(); }
    LAPoly interpolant;
    Strictness strictness = Strictness::NONSTRICT;
    SRef sumSort = SRef_Undef;
    std::vector<PTRef> auxVars;
    for (auto const & term : system) {
        if (sumSort == SRef_Undef) { sumSort = term.sort; }
        // `term.s` already carries its Farkas coefficient (pre-scaled by the caller).
        interpolant.merge(term.s, Real{1});
        if (term.strictness == Strictness::STRICT) { strictness = Strictness::STRICT; }
        for (PTRef x : term.auxVars) {
            if (std::find(auxVars.begin(), auxVars.end(), x) == auxVars.end()) { auxVars.push_back(x); }
        }
    }
    assert(sumSort != SRef_Undef);

    // Record the paper's LA(s, k, F) parameters for every mixed auxiliary variable that survived the
    // summation (an aux var cancels when both split halves of its literal are present). `interpolant`
    // is the body of the "0 <= interpolant" form that toInequality emits, so in the paper's "s <| 0"
    // orientation the coefficient of `x` in `s` is the negation of its coefficient here. The leaf
    // value of k is -e, written -1 in the integer case (see MixedLAInfo). Step 3 (rule-la, in
    // LASolver::resolveMixed) consumes this; the emitted term below is unchanged.
    bool const strict = strictness == Strictness::STRICT;
    for (PTRef x : auxVars) {
        auto it = interpolant.findTermForVar(x);
        if (it == interpolant.end() or it->coeff.isZero()) { continue; }
        mixedLAInfos.push_back(MixedLAInfo{x, -it->coeff, Real{-1}, strict});
    }

    return toInequality(std::move(interpolant), logic, sumSort, strictness);
}

MixedSplit FarkasInterpolator::splitMixedLiteral(PTRef leq) {
    assert(logic.isLeq(leq));
    assert(getColorFor(leq) == icolor_t::I_MIXED);
    // Canonical form of a Leq atom is "0 <= poly"
    SRef const sort = logic.getSortRef(logic.getPterm(leq)[1]);
    LAPoly const poly = ptrefToPoly(leq, logic);

    // Fresh shared (AB) variable used to connect the two halves of the split
    std::string const name = ".mixed_" + std::to_string(leq.x);
    PTRef const x = logic.mkVar(sort, name.c_str());

    // poly = A_part + B_part, where A_part contains only A-local variables and
    // B_part contains B-local and AB (shared) variables, including the constant term
    LAPoly polyA;
    LAPoly polyB;
    int aCount = 0;
    int bCount = 0;
    for (auto const & [var, coeff] : poly) {
        if (var == PTRef_Undef) {
            polyB.addTerm(var, coeff);
            continue;
        }
        icolor_t varColor = icolor_t::I_AB;
        if (logic.isMod(logic.getSymRef(var)) or logic.isIntDiv(var)) {
            Pterm const & p = logic.getPterm(var);
            for (int i = 0; i < p.size(); ++i) {
                if (logic.isVar(p[i])) { varColor = getColorFor(p[i]); }
            }
        } else {
            varColor = getColorFor(var);
        }
        if (varColor == icolor_t::I_A) {
            ++aCount;
            polyA.addTerm(var, coeff);
        } else {
            assert(varColor == icolor_t::I_B or varColor == icolor_t::I_AB);
            if (varColor == icolor_t::I_B) { ++bCount; }
            polyB.addTerm(var, coeff);
        }
    }
    // 0 <= A_part + x        (colorable for A: only A-local vars and the shared x)
    // 0 <= B_part + const - x (colorable for B: only B-local/shared vars and the shared x)
    // Summing the two recovers the original literal: 0 <= A_part + B_part + const
    polyA.addTerm(x, -1);
    polyB.addTerm(x, 1);

    MixedSplit result;
    result.sort = sort;
    // TODO: Think about it -- when one side has no local variables there is nothing genuinely
    // mixed to separate, so fall back to the original literal on both sides.
    if (aCount == 0 || bCount == 0) {
        result.aPart = poly;
        result.bPart = poly;
        result.trivial = true;
        return result;
    }
    result.aPart = std::move(polyA);
    result.bPart = std::move(polyB);
    result.auxVar = x;
    result.auxCoeff = 1; // step 2: replace with the cut divisor for LIA
    return result;
}

PTRef FarkasInterpolator::getFarkasInterpolant(icolor_t color) {
    mixedLAInfos.clear();
    std::vector<LATerm> system;

    // Add one `LA(s <| 0, k)` term to the system: `half` is the shared/aux polynomial, `auxVars`
    // are the fresh mixed variables it still contains (empty for non-mixed literals). The Farkas
    // coefficient (and the sign of a negated literal) is folded into `half` here.
    auto addTerm = [&](LAPoly half, Real const & coeff, bool negated, std::vector<PTRef> auxVars, SRef sort) {
        half.multiplyBy(negated ? -coeff : coeff);
        LATerm term;
        term.s = std::move(half);
        term.strictness = negated ? Strictness::STRICT : Strictness::NONSTRICT;
        term.k = 0; // step 2 populates this from the cut divisor
        term.auxVars = std::move(auxVars);
        term.sort = sort;
        system.push_back(std::move(term));
    };

    for (int i = 0; i < explanations.size(); ++i) {
        PtAsgn const expl = explanations[i];
        Real const coeff = explanation_coeffs[i];
        bool const negated = expl.sgn == l_False;
        icolor_t const litColor = getColorFor(expl.tr);
        if (litColor == color or litColor == icolor_t::I_AB) {
            addTerm(ptrefToPoly(expl.tr, logic), coeff, negated, {}, logic.getUniqueArgSort(expl.tr));
        } else if (litColor == icolor_t::I_MIXED) {
            MixedSplit split = splitMixedLiteral(expl.tr);
            LAPoly half = (color == icolor_t::I_A) ? std::move(split.aPart) : std::move(split.bPart);
            std::vector<PTRef> auxVars;
            if (split.auxVar != PTRef_Undef) { auxVars.push_back(split.auxVar); }
            addTerm(std::move(half), coeff, negated, std::move(auxVars), split.sort);
        }
    }
    PTRef itp = weightedSum(system);
    assert(itp != PTRef_Undef);
    return color == icolor_t::I_B ? logic.mkNot(itp) : itp;
}

PTRef FarkasInterpolator::getFlexibleInterpolant(Real strengthFactor) {
    if (strengthFactor < 0 or strengthFactor >= 1) { throw ApiException("LRA strength factor has to be in [0,1)"); }
    std::vector<std::pair<PtAsgn, Real>> systemA;
    std::vector<std::pair<PtAsgn, Real>> systemB;
    for (int i = 0; i < explanations.size(); ++i) {
        auto litColor = getColorFor(explanations[i].tr);
        if (litColor == icolor_t::I_A or
            litColor ==
                icolor_t::I_AB) { // We put shared literals to A (arbitrary decision, but cannot be in both A and B)
            systemA.emplace_back(explanations[i], explanation_coeffs[i]);
        } else if (litColor == icolor_t::I_B) {
            systemB.emplace_back(explanations[i], explanation_coeffs[i]);
        }
    }
    PTRef itpA = weightedSum(systemA);
    if (itpA == logic.getTerm_true() or itpA == logic.getTerm_false()) {
        assert(itpA == logic.mkNot(weightedSum(systemB)));
        return itpA;
    }
    PTRef itpB = weightedSum(systemB);
    auto extractSides = [this](PTRef inequality) {
        assert(logic.isLeq(inequality) or logic.isLeq(logic.mkNot(inequality)));
        bool negated = logic.isNot(inequality);
        PTRef positive = negated ? logic.mkNot(inequality) : inequality;
        PTRef term = logic.getTermFromLeq(positive);
        PTRef constant = logic.getConstantFromLeq(positive);
        return negated ? std::make_pair(logic.mkNeg(term), logic.mkNeg(constant)) : std::make_pair(term, constant);
    };
    auto sidesA = extractSides(itpA);
    auto sidesB = extractSides(itpB);
    assert(sidesA.first == logic.mkNeg(sidesB.first));
    Real c1 = logic.getNumConst(sidesA.second);
    Real c2 = logic.getNumConst(sidesB.second);
    Real lowerBound = c1;
    Real upperBound = -c2;
    Real strengthDiff = upperBound - lowerBound;
    Real newConstant = lowerBound + (strengthDiff * strengthFactor);
    SRef itpSort = logic.getSortRef(sidesA.first);
    PTRef itp = logic.mkLeq(logic.mkConst(itpSort, newConstant), sidesA.first);
    return itp;
}

bool FarkasInterpolator::ensureHasColorForAllTerms() {
    if (termColorInfo) { return true; }
    if (labels.empty()) { return false; }
    termColorInfo.reset(new LocalTermColorInfo(labels, logic));
    return true;
}
} // namespace opensmt
