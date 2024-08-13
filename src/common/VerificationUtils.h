/*
 *  Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_VERIFICATIONUTILS_H
#define OPENSMT_VERIFICATIONUTILS_H

#include <logics/Logic.h>

namespace opensmt {
class VerificationUtils {
public:
    VerificationUtils(Logic & logic) : logic(logic) {}

    // Verify interpolant internally, using OpenSMT's MainSolver
    bool verifyInterpolantInternal(PTRef partA, PTRef partB, PTRef itp);

    // Verify validity of implication `antecedent -> consequent`, using OpenSMT's MainSolver
    bool impliesInternal(PTRef antecedent, PTRef consequent);

private:
    bool checkSubsetCondition(PTRef p1, PTRef p2) const;

    Logic & logic;
};
} // namespace opensmt

#endif // OPENSMT_VERIFICATIONUTILS_H
