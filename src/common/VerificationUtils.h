/*
 *  Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_VERIFICATIONUTILS_H
#define OPENSMT_VERIFICATIONUTILS_H

#include "Logic.h"

class VerificationUtils {
    Logic & logic;
public:
    VerificationUtils(Logic & logic) : logic(logic) {}

    bool verifyInterpolantInternal(PTRef partA, PTRef partB, PTRef itp); // Verify interpolant internally, using OpenSMT's MainSolver

    bool impliesInternal(PTRef antecedent, PTRef consequent); // Verify validity of implication `antecedent -> consequent`, using OpenSMT's MainSolver

private:
    bool checkSubsetCondition(PTRef p1, PTRef p2) const;
};



#endif //OPENSMT_VERIFICATIONUTILS_H
