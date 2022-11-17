//
// Created by Martin Blicha on 06.11.20.
//

#ifndef OPENSMT_LIAINTERPOLATOR_H
#define OPENSMT_LIAINTERPOLATOR_H

#include "FarkasInterpolator.h"

using ItpColorMap = TheoryInterpolator::ItpColorMap;

struct LAExplanations {
    vec<PtAsgn> explanations;
    std::vector<opensmt::Real> coeffs;
    ItpColorMap labels;

    static LAExplanations getLIAExplanation(ArithLogic & logic, vec<PtAsgn> const & explanations,
                                             std::vector<opensmt::Real> const & coeffs,
                                             ItpColorMap const & labels);
};

class LIAInterpolator : public FarkasInterpolator {

public:
    LIAInterpolator(ArithLogic & logic, LAExplanations liaExplanations);
};


#endif //OPENSMT_LIAINTERPOLATOR_H
