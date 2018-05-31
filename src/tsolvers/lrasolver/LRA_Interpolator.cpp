//
// Created by Martin Blicha on 22.05.18.
//

#include <unordered_map>
#include "LRA_Interpolator.h"
#include <Real.h>
#include <LA.h>
#include <unordered_set>

using namespace opensmt;

using matrix_t = std::vector<std::vector<Real>>;

// TODO: when is explanation negated?
struct ItpHelper {
    ItpHelper(LRALogic & logic, PtAsgn ineq, Real coeff) : explanation{ineq.tr}, negated{ineq.sgn == l_False},
                                                           expl_coeff{std::move(coeff)}, expr{logic, ineq.tr, false} {}
//    ItpHelper(ItpHelper&& other) = default;
//    ItpHelper(const ItpHelper& other) = default;
//    ItpHelper & operator=(ItpHelper&& other) = default;
//    ItpHelper & operator=(const ItpHelper& other) = default;

    PTRef explanation;
    bool negated;
    Real expl_coeff;
    LAExpression expr;
};

namespace {

    std::size_t getPivotRow(const matrix_t & matrix, std::size_t pivotCol, std::size_t startRow) {
        for (auto i = startRow; i < matrix.size(); ++i) {
            if (matrix[i][pivotCol] != 0) {
                return i;
            }
        }
        return matrix.size();
    }

    void addToWithCoeff(std::vector<Real> & to, std::vector<Real> const & what, const Real coeff) {
        assert(to.size() == what.size());
        for (auto i = 0; i < what.size(); ++i) {
            to[i] += coeff * what[i];
        }
    }

    // assumes there are 0 on all position before col
    void normalize(std::vector<Real> & row, std::size_t col) {
#ifndef NDEBUG
        for (auto i = 0; i < col; ++i) {
            assert(row[i] == 0);
        }
#endif //NDEBUG
        auto val = row[col].inverse();
        for (; col < row.size(); ++col) {
            row[col] *= val;
        }
    }

    // assumes matrix is already in row echolon form
    void toReducedRowEcholonForm(std::vector<std::vector<Real>> & matrix) {
        std::vector<std::size_t> pivotColInds;
        std::size_t column = 0;
        for (auto & row : matrix) {
            while (row[column].isZero()) { ++column; }
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
            for (int rowInd2 = rowInd - 1; rowInd2 >= 0; --rowInd2) {
                if (matrix[rowInd2][column].isZero()) { continue; }
                addToWithCoeff(matrix[rowInd2], row, -matrix[rowInd2][column]);
            }

        }
    }

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
                for (auto col = 0; col <= pivotCol; ++col) {
                    assert(matrix[row][col] == 0);
                }
#endif // NDEBUG
            }
            ++pivotRow;
            ++pivotCol;
        }
    }

    std::size_t getNullity(std::vector<std::vector<Real>> const & matrix) {
        // nullity is the number of columns - rank
        auto rank = std::count_if(matrix.cbegin(), matrix.cend(), [](std::vector<Real> const & row) {
            return std::any_of(row.cbegin(), row.cend(), [](Real const & r) { return r != 0; });
        });
        auto cols = matrix[0].size();
        assert(cols >= rank);
        return cols - rank;
    }

    // assumes the matrix is in echolon form; reurns bitmap which columns contain pivot
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

    // assumes matrix is in reduced row echolon form
    // check the algorithm at wiki: https://en.wikibooks.org/wiki/Linear_Algebra/Null_Spaces
    std::vector<std::vector<Real>> getNullBasis(std::vector<std::vector<Real>> const & matrix) {
        std::vector<std::vector<Real>> basis;
        auto pivotColsBitMap = getPivotColsBitMap(matrix);
        auto cols = matrix[0].size();
        // for non-pivot columns generate a new base vector
        for (std::size_t col = 0; col < cols; ++col) {
            if (pivotColsBitMap[col]) {
                continue;
            }
            basis.emplace_back();
            auto & base_vector = basis.back();

            // keep track of current row (with the pivot)
            auto row = static_cast<int>(matrix.size() - 1);
            // compute solution for a vector where pivotal columns have unknown,
            // current non-pivotal column has 1 and other non-pivotal columns has 0
            for (auto sol_col = static_cast<int>(cols - 1); sol_col >= 0; --sol_col) {
                assert(row >= 0 && row < matrix.size());
                assert(cols - (sol_col + 1) ==
                       base_vector.size()); // we already have solutions for all the following columns
                if (!pivotColsBitMap[sol_col]) {
                    base_vector.emplace_back(sol_col == col ? 1 : 0);
//                    solution.insert(std::make_pair(sol_col, sol_col == col ? 1 : 0));
                } else {
                    // pivotal column -> go over the following columns for which we already have solutions
                    assert(matrix[row][sol_col] == 1); // pivot
                    Real column_solution{0};
                    for (int i = sol_col + 1; i < cols; ++i) {
                        // iterate over the row after the pivot position and multiply minus coefficient with solution of the corresponding column, sum everything
                        std::size_t sol_index = base_vector.size() - (i - sol_col);
                        assert(sol_index >= 0 && sol_index < base_vector.size());
                        column_solution += (-matrix[row][i]) * (base_vector[sol_index]);
//                        std::cout << "Current solution is " << column_solution << '\n';
                    }
                    base_vector.push_back(column_solution);
                    --row;
                }
            }
            // we have pushed solutions starting from back, so we have to reverse
            std::reverse(base_vector.begin(), base_vector.end());
            // we are done, the basis vector is already in result
            assert(base_vector.size() == cols);
        }
        return basis;
    }

    bool containsNegative(std::vector<Real> const & vec){
        return std::any_of(vec.begin(), vec.end(), [](const Real & val) { return val < 0; });
    }

    bool tryFixVec(std::vector<Real> & vec, std::vector<std::vector<Real>> & basis){
        auto neg = std::find_if(vec.begin(), vec.end(), [](const Real& val) {return val < 0;});
        assert(neg != vec.end());
        auto offset = neg - vec.begin();
        auto canFixNegative = [offset](const std::vector<Real> & other){
            return other[offset] > 0 && !containsNegative(other);
        };
        auto fixer_it = std::find_if(basis.begin(), basis.end(), canFixNegative);
        if(fixer_it == basis.end()) {return false;}
        auto const & fixer = *fixer_it;
        addToWithCoeff(vec, fixer, -(vec[offset]/(fixer)[offset]));
        assert(vec[offset].isZero());
        return true;
    }

    // TODO: make this more efficient if necessary
    bool tryFixBase(std::vector<std::vector<Real>> & basis){
        auto first_unchecked_it = basis.begin();
        auto vec_with_neg_it = first_unchecked_it;
        while(vec_with_neg_it != basis.end()){
            vec_with_neg_it = std::find_if(first_unchecked_it, basis.end(), containsNegative);
            if(vec_with_neg_it == basis.end()){
                return true;
            }
            bool wasFixed = tryFixVec(*vec_with_neg_it, basis);
            if(!wasFixed){
                return false;
            }
            first_unchecked_it = vec_with_neg_it;
        }
        return true;
    }

    bool check_basis(std::vector<std::vector<FastRational>> const & basis){
        return std::all_of(basis.begin(), basis.end(), [](std::vector<Real> const & baseVec){
            return std::none_of(baseVec.begin(), baseVec.end(), [](const Real& el){return el < 0;});
        });
    }

    void print_matrix(std::vector<std::vector<Real>> const & matrix) {
        for (auto const & row : matrix) {
            for (auto const & elem : row) {
                std::cout << elem << " ";
            }
            std::cout << '\n';
        }
        std::cout << '\n';
    }

    void print_basis(std::vector<std::vector<FastRational>> const & nullBasis) {
        std::cout << "Basis: " << '\n';
        for (auto const & base : nullBasis) {
            for (auto const & elem : base) {
                std::cout << elem << ' ';
            }
            std::cout << '\n';
        }
        std::cout << '\n';
    }


    PTRef sumInequalities(std::vector<ItpHelper> const & ineqs, std::vector<Real> const & coeffs, LRALogic & logic) {
        assert(ineqs.size() == coeffs.size());
        LAExpression init{logic};
        auto it_ineq = ineqs.begin();
        auto it_coeff = coeffs.begin();
        bool delta_flag = false;
        for (; it_ineq != ineqs.end(); ++it_ineq, ++it_coeff) {
            auto const & ineq = *it_ineq;
            if (ineq.negated) {
                delta_flag = true;
                init.addExprWithCoeff(ineq.expr, -(*it_coeff));
            } else {
                init.addExprWithCoeff(ineq.expr, *it_coeff);
            }
//            init.print(std::cout);
        }
        // here we have to compensate for the fact that we used LAexpression to compute the coefficients, so everything is multiplied by -1
        // therefore we need to create the inequality with the terms on LHS, because they are treated like LHS when LAExpressions are created
        PTRef rhs = logic.mkConst("0");
        PTRef lhs = init.toPTRef();
        return delta_flag ? logic.mkRealLt(lhs, rhs) : logic.mkRealLeq(lhs, rhs);
    }

    PTRef sumInequalities(std::vector<ItpHelper> const & ineqs, LRALogic & logic) {
        std::vector<Real> coeffs;
        coeffs.reserve(ineqs.size());
        for (const auto & helper : ineqs) {
            coeffs.push_back(helper.expl_coeff);
        }
        return sumInequalities(ineqs, coeffs, logic);
    }
}


PTRef LRA_Interpolator::getInterpolant(icolor_t color) {
    // this will be contain the result, inequalities corresponding to summed up partitions of explanataions (of given color)
    std::vector<PTRef> interpolant_inequalities;
    std::vector<std::pair<PtAsgn, Real>> candidates;
    assert(explanations.size() == explanation_coeffs.size());
    for (std::size_t i = 0; i < explanations.size(); ++i) {
        candidates.emplace_back(explanations[i], explanation_coeffs[i]);
//        std::cout << "Explanation " << logic.printTerm(explanations[i].tr) << " with coeff "
//                  << explanation_coeffs[i] << " is negated: " << (explanations[i].sgn == l_False) << '\n';
        bool isA = this->isInPartitionOfColor(icolor_t::I_A, explanations[i].tr);
        bool isB = this->isInPartitionOfColor(icolor_t::I_B, explanations[i].tr);
        if(isA){
//            std::cout << "This explanation is from A\n";
        }
        if(isB){
//            std::cout << "This explanation is from B\n";
        }

    }
    auto it = std::partition(candidates.begin(), candidates.end(),
                             [color, this](std::pair<PtAsgn, Real> const & expl) {
                                 return this->isInPartitionOfColor(color, expl.first.tr);
                             });

    std::vector<ItpHelper> helpers;
    LRALogic & logic = this->logic;
    std::transform(candidates.begin(), it, std::back_inserter(helpers),
                   [&logic](std::pair<PtAsgn, Real> const & expl) {
                       return ItpHelper{logic, expl.first, expl.second};
                   });

    using local_vars_info = std::vector<std::pair<PTRef, FastRational>>;
    // create information about local variables for each inequality
    std::vector<local_vars_info> ineqs_local_vars;
    std::vector<ItpHelper> explanations_with_locals;
    std::vector<Real> explanations_with_locals_coeffs;
    for (const auto & helper : helpers) {
        local_vars_info local_vars;
        for (auto factor : helper.expr) {
            auto var_ref = factor.first;
            if (var_ref != PTRef_Undef) {
                if (isLocalFor(color, var_ref)) {
                    auto coeff = factor.second;
                    if (helper.negated) {
                        coeff.negate();
                    }
//                    std::cout << "In " << logic.printTerm(helper.explanation) << " coeff for var " << logic.printTerm(var_ref) << " is " << coeff << '\n';
//                    std::cout << "LAExpression:\n";
//                    helper.expr.print(std::cout);
                    local_vars.emplace_back(var_ref, coeff);
                }
            }
        }
        // explanataion with all variables shared form standalone partition
        if (local_vars.empty()) {
            interpolant_inequalities.push_back(helper.negated ? logic.mkNot(helper.explanation) : helper.explanation);
        }
            // for explanations with local variables, remember them separately
        else {
            ineqs_local_vars.push_back(std::move(local_vars));
            explanations_with_locals.push_back(helper);
        }
    }

    if (!ineqs_local_vars.empty()) {
        // assign index to each local var
        std::unordered_map<PTRef, std::size_t, PTRefHash> local_vars;
        for (const auto & info : ineqs_local_vars) {
            for (auto const & factor : info) {
                if (local_vars.find(factor.first) == local_vars.end()) {
                    auto size = local_vars.size();
                    local_vars[factor.first] = size;
                }
            }
        }
        // create a matrix from those containing local variables
        // rows correspond to local variables, columns correspond to explanations (inequalities)

        matrix_t matrix{local_vars.size()};
        auto colInd = 0;
        for (const auto & info : ineqs_local_vars) {
            // add coefficient to those rows whose corresponding variable occurs in the inequality
            for (auto const & coeff_var : info) {
                auto var = coeff_var.first;
                auto ind = local_vars[var];
                matrix[ind].push_back(coeff_var.second);
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
//        print_matrix(matrix);
        gaussianElimination(matrix);
//        print_matrix(matrix);
        auto nullity = getNullity(matrix);
        // if the space of solutions does not have at least two vector in basis, we cannot do anything
        if (nullity <= 1) {
//            std::cout << "Nullity space has single-vector basis" << '\n';
            interpolant_inequalities.push_back(sumInequalities(explanations_with_locals, logic));
        } else {
            toReducedRowEcholonForm(matrix);
//            print_matrix(matrix);
            auto nullBasis = getNullBasis(matrix);
            // print the basis vectors:
//            print_basis(nullBasis);
            bool isGood = tryFixBase(nullBasis);
            if(!isGood){
                // default behaviour, sum up with original coefficient
                interpolant_inequalities.push_back(sumInequalities(explanations_with_locals, logic));
            }
            else{
                assert(check_basis(nullBasis));
                // foreach vector in the basis, cycle over the inequalities and sum it all up, with corresponding coefficient
                for (const auto & base : nullBasis) {
                    interpolant_inequalities.push_back(sumInequalities(explanations_with_locals, base, logic));
                }
            }
        }
    }
    else{
        assert(explanations_with_locals.empty());
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
