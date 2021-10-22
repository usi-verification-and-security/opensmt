//
// Created by Martin Blicha on 06.11.20.
//

#include "LIAInterpolator.h"
#include "ArithLogic.h"

#include <memory>

LAExplanations LAExplanations::getLIAExplanation(ArithLogic & logic, vec<PtAsgn> const & explanations,
                                                  std::vector<opensmt::Real> const & coeffs,
                                                  std::map<PTRef, icolor_t> const & labels) {
    LAExplanations liaExplanations;
    // We need to recompute the labels for the Farkas interpolator!
    // Consider this example: not (0 <= x - y) with label A; not (1 <= y - x) with label B
    // After strengthening we get 1 <= y - x with label A; 0 <= x - y with label B
    // The labels have been switched for the positive atoms, and we need to make sure that interpolator sees the second version of the labels
    for (auto explEntry : explanations) {
        PTRef positiveInequality = explEntry.tr;
        lbool sign = explEntry.sgn;
        assert(logic.isNumLeq(positiveInequality));
        assert(sign == l_True or sign == l_False);
        PTRef boundVal = logic.getConstantFromLeq(positiveInequality);
        PTRef boundedTerm = logic.getTermFromLeq(positiveInequality);
        assert(logic.isNumConst(boundVal) and logic.isLinearTerm(boundedTerm));
        assert(logic.getNumConst(boundVal).isInteger()); // We assume LIA inequalities are already strengthened
        if (sign == l_True) {
            // Already strengthened!
            liaExplanations.explanations.push(PtAsgn(positiveInequality, l_True));
        } else {
            // 'not (c <= term)' => 'c > term' => 'term < c' => 'term <= c-1' => -(c-1) <= -term
            auto newBoundValue = (logic.getNumConst(boundVal) - 1);
            newBoundValue.negate();
            PTRef nInequality = logic.mkNumLeq(logic.mkConst(newBoundValue), logic.mkNumNeg(boundedTerm));
            assert(logic.getTermFromLeq(nInequality) == logic.mkNumNeg(boundedTerm));
            liaExplanations.explanations.push(PtAsgn(nInequality, l_True));
        }
        // Ensure the strengthened inequality has correct partition information
        PTRef nInequality = liaExplanations.explanations.last().tr;
        auto res = liaExplanations.labels.insert(std::make_pair(nInequality, labels.at(positiveInequality)));
        if (not res.second) {
            // key has been already present
            throw OsmtInternalException("Error in preparing LIA interpolation");
        }
    }
    liaExplanations.coeffs = coeffs;
    return liaExplanations;
}

LIAInterpolator::LIAInterpolator(ArithLogic & logic, LAExplanations liaExplanations)
    : FarkasInterpolator(logic, std::move(liaExplanations.explanations), std::move(liaExplanations.coeffs), std::move(liaExplanations.labels))
    { }
