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
};

class LIAInterpolator : public FarkasInterpolator {
public:
    LIAInterpolator(ArithLogic & logic, LAExplanations liaExplanations);
};
} // namespace opensmt

#endif // OPENSMT_LIAINTERPOLATOR_H
