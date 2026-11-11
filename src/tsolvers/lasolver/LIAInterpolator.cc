//
// Created by Martin Blicha on 06.11.20.
//

#include "LIAInterpolator.h"

#include <logics/ArithLogic.h>

#include <memory>

namespace opensmt {
LAExplanations LAExplanations::getLIAExplanation(ArithLogic & logic, vec<PtAsgn> const & explanations,
                                                 std::vector<Real> const & coeffs, ItpColorMap const & labels) {
    LAExplanations liaExplanations;
    // We need to recompute the labels for the Farkas interpolator!
    // Consider this example: not (0 <= x - y) with label A; not (1 <= y - x) with label B
    // After strengthening we get 1 <= y - x with label A; 0 <= x - y with label B
    // The labels have been switched for the positive atoms, and we need to make sure that interpolator sees the
    // second version of the labels
    for (auto explEntry : explanations) {
        PTRef positiveInequality = explEntry.tr;
        liaExplanations.explanations.push(strengthen(logic, explEntry));
        // Ensure the strengthened inequality has correct partition information
        PTRef nInequality = liaExplanations.explanations.last().tr;
        auto res = liaExplanations.labels.insert(std::make_pair(nInequality, labels.at(positiveInequality)));
        if (not res.second) {
            // key has been already present
            throw InternalException("Error in preparing LIA interpolation");
        }
    }
    liaExplanations.coeffs = coeffs;
    return liaExplanations;
}

PtAsgn LAExplanations::strengthen(ArithLogic & logic, PtAsgn literal) {
    PTRef const positiveInequality = literal.tr;
    lbool const sign = literal.sgn;
    assert(logic.isLeq(positiveInequality));
    assert(sign == l_True or sign == l_False);
    PTRef const boundVal = logic.getConstantFromLeq(positiveInequality);
    PTRef const boundedTerm = logic.getTermFromLeq(positiveInequality);
    assert(logic.isNumConst(boundVal) and logic.isLinearTerm(boundedTerm));
    assert(logic.getNumConst(boundVal).isInteger()); // We assume LIA inequalities are already strengthened
    if (sign == l_True) {
        // Already strengthened!
        return PtAsgn(positiveInequality, l_True);
    }
    // 'not (c <= term)' => 'c > term' => 'term < c' => 'term <= c-1' => -(c-1) <= -term
    auto newBoundValue = (logic.getNumConst(boundVal) - 1);
    newBoundValue.negate();
    PTRef const nInequality = logic.mkLeq(logic.mkIntConst(newBoundValue), logic.mkNeg(boundedTerm));
    assert(logic.getTermFromLeq(nInequality) == logic.mkNeg(boundedTerm));
    return PtAsgn(nInequality, l_True);
}

LIAInterpolator::LIAInterpolator(ArithLogic & logic, LAExplanations liaExplanations,
                                 std::unique_ptr<TermColorInfo> colorInfo)
    : FarkasInterpolator(logic, std::move(liaExplanations.explanations), std::move(liaExplanations.coeffs),
                         std::move(liaExplanations.labels), std::move(colorInfo)) {}

LIAInterpolator::LIAInterpolator(ArithLogic & logic, LAExplanations liaExplanations)
    : FarkasInterpolator(logic, std::move(liaExplanations.explanations), std::move(liaExplanations.coeffs),
                         std::move(liaExplanations.labels)) {}
} // namespace opensmt
