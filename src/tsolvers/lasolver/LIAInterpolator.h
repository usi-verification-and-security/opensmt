//
// Created by Martin Blicha on 06.11.20.
//

#ifndef OPENSMT_LIAINTERPOLATOR_H
#define OPENSMT_LIAINTERPOLATOR_H

#include "FarkasInterpolator.h"

namespace opensmt {
using ItpColorMap = TheoryInterpolator::ItpColorMap;

struct LAExplanations {
    vec<PtAsgn> explanations;
    std::vector<Real> coeffs;
    ItpColorMap labels;

    static LAExplanations getLIAExplanation(ArithLogic & logic, vec<PtAsgn> const & explanations,
                                            std::vector<Real> const & coeffs, ItpColorMap const & labels);

    /// LIA strengthening of an explanation literal over an integer Leq atom: 'not (c <= t)' becomes the positive
    /// '-(c-1) <= -t'; a positive literal is returned unchanged.
    static PtAsgn strengthen(ArithLogic & logic, PtAsgn literal);
};

class LIAInterpolator : public FarkasInterpolator {
public:
    LIAInterpolator(ArithLogic & logic, LAExplanations liaExplanations, std::unique_ptr<TermColorInfo> colorInfo);
    LIAInterpolator(ArithLogic & logic, LAExplanations liaExplanations);

    // not implemented for integers
    PTRef getFlexibleInterpolant(Real strengthFactor) = delete;
};
} // namespace opensmt

#endif // OPENSMT_LIAINTERPOLATOR_H
