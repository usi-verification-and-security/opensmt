//
// Created by Martin Blicha on 22.05.18.
//

#ifdef PRODUCE_PROOF

//#ifndef NDEBUG
//#define TRACE
//#endif

#ifdef TRACE
#define trace(x) x
#else
#define trace(x)
#endif


#include "LRA_Interpolator.h"
#include "LRALogic.h"
#include <Real.h>
#include <LA.h>
#include <unordered_set>
#include <unordered_map>
#include <functional>

using namespace opensmt;

using matrix_t = std::vector<std::vector<Real>>;

// initializing static member
DecomposedStatistics LRA_Interpolator::stats {};

namespace {

// TODO: when is explanation negated?
struct ItpHelper {
    ItpHelper(LALogic & logic, PtAsgn ineq, Real coeff) : explanation(ineq.tr), negated(ineq.sgn == l_False),
                                                          expl_coeff(std::move(coeff)), expr(logic, ineq.tr, false) {}
    PTRef explanation;
    bool negated;
    Real expl_coeff;
    LAExpression expr;
};

struct LinearTerm {
    LinearTerm(PTRef var_, Real coeff_): var(var_), coeff(std::move(coeff_)) {}
    PTRef var;
    Real coeff;
};

using Basis = std::vector<std::vector<Real>>;
using Coordinates = std::vector<Real>;

std::vector<LinearTerm> getLocalTerms(ItpHelper const & helper, std::function<bool(PTRef)> isLocal){
    std::vector<LinearTerm> res;
    for (auto factor : helper.expr) {
        auto var_ref = factor.first;
        if (var_ref != PTRef_Undef) {
            if (isLocal(var_ref)) {
                auto coeff = factor.second;
                if (helper.negated) {
                    coeff.negate();
                }
                res.emplace_back(var_ref, coeff);
            }
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
    std::size_t getPivotRow(const matrix_t & matrix, std::size_t pivotCol, std::size_t startRow) {
        for (auto i = startRow; i < matrix.size(); ++i) {
            if (matrix[i][pivotCol] != 0) {
                return i;
            }
        }
        return matrix.size();
    }

    /** Adds a multiple of vector of Reals to another vector with equal size.
     *
     * @param to vector to which we add
     * @param what vector being added
     * @param coeff The multiple
     */
    void addToWithCoeff(std::vector<Real> & to, std::vector<Real> const & what, const Real & coeff) {
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
#endif //NDEBUG
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
            auto it = std::find_if(row.begin() + column, row.end(), [](const Real & el) {return !el.isZero();});
            if (it == row.end()) {continue;}
            column = it - row.begin();
            assert(pivotColInds.empty() || pivotColInds.back() < column);
            pivotColInds.push_back(column);
            if (row[column] != 1) {
                normalize(row, column);
            }
        }

        // TODO: use long instead of int?
        for (auto rowInd = (int) (matrix.size() - 1); rowInd >= 0; --rowInd) {
            auto & row = matrix[rowInd];
            auto pivotColInd = pivotColInds.back();
            if (row[pivotColInd].isZero()) {
                continue;
            }
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
            if (nextRow != pivotRow) {
                std::swap(matrix[pivotRow], matrix[nextRow]);
            }
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

#ifndef NDEBUG
    bool isReducedRowEchelonForm(std::vector<std::vector<Real>> const & matrix) {
        auto pivotColsBitMap = getPivotColsBitMap(matrix);
        auto cols = pivotColsBitMap.size();
        assert(cols == matrix[0].size());
        std::size_t pivotRow = 0;
        for (unsigned int col = 0; col < pivotColsBitMap.size(); ++col) {
            if(pivotColsBitMap[col]) {
                for (std::size_t row = 0; row < matrix.size(); ++row) {
                    if ((row != pivotRow && matrix[row][col] != 0) || (row == pivotRow && matrix[row][col] != 1)) {
                        return false;
                    }
                }
                ++pivotRow;
            }
            else { // free column (not pivot)
                for (auto row = pivotRow; row < matrix.size(); ++row) {
                    if (matrix[row][col] != 0) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    bool check_basis(std::vector<std::vector<FastRational>> const & basis) {
        return std::all_of(basis.begin(), basis.end(), [](std::vector<Real> const & baseVec) {
            return std::none_of(baseVec.begin(), baseVec.end(), [](const Real & el) { return el < 0; });
        });
    }

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

    void print_basis(std::vector<std::vector<FastRational>> const & nullBasis) {
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
#endif // NDEBUG

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
            if (pivotColsBitMap[col]) {
                continue;
            }
            basis.emplace_back();
            auto & base_vector = basis.back();

            // put 1 on position of this free column, 0 on positions of other free columns, and -val at pivot row
            unsigned int pivotRow = 0;
            for (unsigned int colPos = 0; colPos < cols; ++colPos) {
                if (pivotColsBitMap[colPos]) {
                    base_vector.push_back(-matrix[pivotRow][col]);
                    ++pivotRow;
                }
                else { // free column
                    base_vector.push_back(colPos == col ? 1 : 0);
                }
            }
        }
        return basis;
    }

//    MB: the methods commented out represent the old, incomplete approach
//    bool containsNegative(std::vector<Real> const & vec){
//        return std::any_of(vec.begin(), vec.end(), [](const Real & val) { return val < 0; });
//    }
//
//
//    /*
//     * Tries to replace a vector in basis with a negative coordinate with another vector having less negative coordinates.
//     */
//    bool tryFixVec(std::size_t idx, std::vector<std::vector<Real>> & basis, std::vector<Real> & alphas){
//        assert(std::all_of(alphas.begin(), alphas.end(), [](const Real & val) {return val > 0;}));
//        auto & vec = basis[idx];
//        auto neg = std::find_if(vec.begin(), vec.end(), [](const Real& val) {return val < 0;});
//        assert(neg != vec.end());
//        auto position = neg - vec.begin();
//        auto fixer_it = basis.begin();
//        Real diff{0};
//        for( ; fixer_it != basis.end(); ++fixer_it) {
//            auto const & fixCandidate = *fixer_it;
//            if (fixCandidate[position] > 0 && !containsNegative(fixCandidate)) {
//                // OK candidate, check alphas
//                diff = vec[position] / fixCandidate[position];
//                auto fixCandidateIndex = fixer_it - basis.begin();
//                if (alphas[fixCandidateIndex] + diff > 0) {
//                    // OK, the alphas will remain positive
//                    break;
//                }
//            }
//        }
//        if(fixer_it == basis.end()) {return false;}
//        auto const & fixer = *fixer_it;
//        alphas[fixer_it - basis.begin()] += diff;
//        assert(alphas[fixer_it - basis.begin()] > 0);
//        diff.negate();
//        addToWithCoeff(vec, fixer, diff);
//        assert(vec[position].isZero());
//        return true;
//    }
//
//    /*
//     * Given a basis of vector space where some vector contains negative coordinate, it tries to find a different basis
//     * for the space where all coordinates of all vectors of the basis would be non-negative
//     */
//    bool tryFixBase(std::vector<std::vector<Real>> & basis, std::vector<Real> alphas) {
//        auto first_unchecked_it = basis.begin();
//        auto vec_with_neg_it = first_unchecked_it;
//        while(vec_with_neg_it != basis.end()){
//            vec_with_neg_it = std::find_if(first_unchecked_it, basis.end(), containsNegative);
//            if(vec_with_neg_it == basis.end()){
//                return true;
//            }
//            bool wasFixed = tryFixVec((vec_with_neg_it - basis.begin()), basis, alphas);
//            if(!wasFixed){
//                return false;
//            }
//            first_unchecked_it = vec_with_neg_it;
//        }
//        return true;
//    }

    bool isDecomposition(Basis const & basis, Coordinates const & coordinates, std::vector<Real> const& original) {
        assert(coordinates.size() == basis.size());
        assert(std::all_of(basis.begin(), basis.end(),
                [&original](std::vector<Real> const& baseVec) { return baseVec.size() == original.size(); }));
        for (std::size_t i = 0; i < original.size(); ++i) {
            Real sum = 0;
            for(std::size_t j = 0; j < basis.size(); ++j) {
                sum += basis[j][i] * coordinates[j];
            }
            if (sum != original[i]) { return false; }
        }
        return true;
    }


    PTRef sumInequalities(std::vector<ItpHelper> const & ineqs, std::vector<Real> const & coeffs, LALogic & logic) {
        assert(ineqs.size() == coeffs.size());
        LAExpression init{logic};
        auto it_ineq = ineqs.begin();
        auto it_coeff = coeffs.begin();
        bool delta_flag = false;
        for (; it_ineq != ineqs.end(); ++it_ineq, ++it_coeff) {
            auto const & coeff = *it_coeff;
            if(coeff.isZero()) {continue;} // when some basis is found, some coordinates could be zero; ignore those
            auto const & ineq = *it_ineq;
            trace(std::cout << "Original explanation: " << logic.printTerm(ineq.explanation) << "; negated: " << ineq.negated << '\n';)
            trace(std::cout << "LAExpr as PTrEf: " << logic.printTerm(ineq.expr.toPTRef()) << '\n';)
            trace(std::cout << "LAExpr as stored: ";)
            trace(ineq.expr.print(std::cout); std::cout << std::endl;)
            if (ineq.negated) {
                delta_flag = true;
                init.addExprWithCoeff(ineq.expr, -(coeff));
            } else {
                init.addExprWithCoeff(ineq.expr, coeff);
            }
            trace(init.print(std::cout);)
        }
        // here we have to compensate for the fact that we used LAexpression to compute the coefficients, so everything is multiplied by -1
        // therefore we need to create the inequality with the terms on LHS, because they are treated like LHS when LAExpressions are created
        PTRef rhs = logic.mkConst("0");
        PTRef lhs = init.toPTRef();
//        std::cout << "LHS: " << logic.printTerm(lhs) << '\n';
        return delta_flag ? logic.mkNumLt(lhs, rhs) : logic.mkNumLeq(lhs, rhs);
    }

    PTRef sumInequalities(std::vector<ItpHelper> const & ineqs, LALogic & logic) {
        std::vector<Real> coeffs;
        coeffs.reserve(ineqs.size());
        for (const auto & helper : ineqs) {
            coeffs.push_back(helper.expl_coeff);
        }
        return sumInequalities(ineqs, coeffs, logic);
    }

    std::vector<Real> getFarkasCoeffs(std::vector<ItpHelper> const & inequalities) {
        std::vector<Real> ret;
        for (const auto & ineq : inequalities) {
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
            if (!isPivot(i)) {ret.push_back(allFarkasCoeffs[i]);}
        }
        return ret;
    }

    void ensureNonNegativeVec(std::vector<Real> & baseVec, std::size_t baseVecIndex, Coordinates & coordinates,
                              std::vector<Real> const & vecToDecompose) {
        for (std::size_t i = 0; i < baseVec.size(); ++i) {
            if (baseVec[i] < 0) {
                auto coeff = (-baseVec[i] / vecToDecompose[i]);
                // baseVec += coeff * vecToDecompose;
                for (std::size_t j = 0; j < baseVec.size(); ++j) { baseVec[j] += coeff * vecToDecompose[j]; }
                // update coordinates
                Real divisor = Real{1} + (coeff * coordinates[baseVecIndex]);
                for (Real& coordinate : coordinates) { coordinate /= divisor; }
            }
        }
    }

    void ensureNonNegativeDecomposition(Basis& basis, Coordinates & coordinates, std::vector<Real> const & vecToDecompose) {
        for (std::size_t i = 0; i < basis.size(); ++i) {
            ensureNonNegativeVec(basis[i], i, coordinates, vecToDecompose);
        }
    }

    struct StatsHelper{
        bool standAloneIneq = false;
        bool nonTrivialBasis = false;
        bool moreThanOneInequality = false;
    };

}

PTRef LRA_Interpolator::getInterpolant(icolor_t color) {
    assert(color == icolor_t::I_A || color == icolor_t::I_B);
    StatsHelper statsHelper;
    // this will be contain the result, inequalities corresponding to summed up partitions of explanataions (of given color)
    std::vector<PTRef> interpolant_inequalities;
    std::vector<std::pair<PtAsgn, Real>> candidates;
    assert(explanations.size() == static_cast<int>(explanation_coeffs.size()));
    for (int i = 0; i < explanations.size(); ++i) {
        assert(explanation_coeffs[i] > 0);
        candidates.emplace_back(explanations[i], explanation_coeffs[i]);
        trace(std::cout << "Explanation " << logic.printTerm(explanations[i].tr) << " with coeff "
                  << explanation_coeffs[i] << " is negated: " << (explanations[i].sgn == l_False) << '\n';)
        bool isA = this->isInPartitionOfColor(icolor_t::I_A, explanations[i].tr);
        bool isB = this->isInPartitionOfColor(icolor_t::I_B, explanations[i].tr);
        if(isA){
            trace(std::cout << "This explanation is from A\n";)
        }
        if(isB){
            trace(std::cout << "This explanation is from B\n";)
        }

    }
    auto it = std::partition(candidates.begin(), candidates.end(),
                             [color, this](std::pair<PtAsgn, Real> const & expl) {
                                 return this->isInPartitionOfColor(color, expl.first.tr);
                             });
    if (it == candidates.end() || it == candidates.begin()) {
        // all inequalities are of the same color -> trivial interpolant
        // return false for all of color A and true for all of color B
        return ((it == candidates.end() && color == icolor_t::I_A)
                || (it == candidates.begin() && color == icolor_t::I_B))
                ? logic.getTerm_false() : logic.getTerm_true();
    }
    std::vector<ItpHelper> helpers;
    LALogic & logic = this->logic;
    std::transform(candidates.begin(), it, std::back_inserter(helpers),
                   [&logic](std::pair<PtAsgn, Real> const & expl) {
                       return ItpHelper{logic, expl.first, expl.second};
                   });
    statsHelper.moreThanOneInequality = helpers.size() > 1;
    using local_terms_t = std::vector<LinearTerm>;
    // create information about local variables for each inequality
    std::vector<local_terms_t> ineqs_local_vars;
    std::vector<ItpHelper> explanations_with_locals;
    for (const auto & helper : helpers) {
        local_terms_t local_terms = getLocalTerms(helper, [this, color](PTRef ptr) { return this->isLocalFor(color, ptr); });

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
        for (const auto & info : ineqs_local_vars) {
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
        for (const auto & info : ineqs_local_vars) {
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
        trace(print_matrix(matrix);)
        gaussianElimination(matrix);
        trace(print_matrix(matrix);)
        auto nullity = getNullity(matrix);
        // if the space of solutions does not have at least two vector in basis, we cannot do anything
        if (nullity <= 1) {
//            std::cout << "Nullity space has single-vector basis" << '\n';
            interpolant_inequalities.push_back(sumInequalities(explanations_with_locals, logic));
        } else {
            toReducedRowEcholonForm(matrix);
            trace(print_matrix(matrix);)
            auto nullBasis = getNullBasis(matrix);
            trace(print_basis(nullBasis);)
            assert(explanations_with_locals.size() == matrix[0].size());
            auto farkasCoeffs = getFarkasCoeffs(explanations_with_locals);
            const auto pivotColIndexBitMap = getPivotColsBitMap(matrix);
            assert(farkasCoeffs.size() == pivotColIndexBitMap.size());
            auto isPivotColIndex = [&pivotColIndexBitMap](std::size_t index) { return pivotColIndexBitMap[index]; };
            auto alphas = getAlphas(farkasCoeffs, isPivotColIndex);
            assert(std::all_of(alphas.begin(), alphas.end(), [](const Real& v) {return v > 0;}));
            assert(alphas.size() == nullBasis.size());
            assert(isDecomposition(nullBasis, alphas, farkasCoeffs));
            ensureNonNegativeDecomposition(nullBasis, alphas, farkasCoeffs);
            assert(std::all_of(alphas.begin(), alphas.end(), [](const Real& v) {return v > 0;}));
            assert(check_basis(nullBasis));
            assert(isDecomposition(nullBasis, alphas, farkasCoeffs));
            statsHelper.nonTrivialBasis = true;
            // foreach vector in the basis, cycle over the inequalities and sum it all up, with corresponding coefficient
            for (const auto & base : nullBasis) {
                interpolant_inequalities.push_back(sumInequalities(explanations_with_locals, base, logic));
            }
        }
    }
    else{
        assert(explanations_with_locals.empty());
    }

    if (!interpolant_inequalities.empty()) {
        if (statsHelper.moreThanOneInequality) {
            LRA_Interpolator::stats.decompositionOpportunities++;
        }
        if (interpolant_inequalities.size() > 1) {
            LRA_Interpolator::stats.decomposedItps++;
            assert(statsHelper.nonTrivialBasis || statsHelper.standAloneIneq);
            if (statsHelper.nonTrivialBasis) {
                LRA_Interpolator::stats.nonTrivialBasis++;
            }
            if (statsHelper.standAloneIneq) {
                LRA_Interpolator::stats.standAloneIneq++;
            }
        }
    }

    vec<PTRef> args;
    for (auto const & itp : interpolant_inequalities) {
        args.push(itp);
    }
    PTRef itp = logic.mkAnd(args);
    if (color == icolor_t::I_B) {
        itp = logic.mkNot(itp);
    }
    return itp;
}

bool LRA_Interpolator::isALocal(PTRef var) const {
    return isAstrict(logic.getIPartitions(var), mask);
}

bool LRA_Interpolator::isBLocal(PTRef var) const {
    return isBstrict(logic.getIPartitions(var), mask);
}

#endif // PRODUCE_PROOF