//
// Created by Martin Blicha on 29.07.20.
//

#ifndef OPENSMT_VERIFICATIONUTILS_H
#define OPENSMT_VERIFICATIONUTILS_H

#include "SMTConfig.h"
#include "Logic.h"

class VerificationUtils {
    SMTConfig const & config;
    Logic & logic;
public:
    VerificationUtils(SMTConfig const & config, Logic & logic) : config(config), logic(logic) {}

    bool impliesExternal(PTRef, PTRef); // Check the result with an external solver

    bool verifyInterpolantExternal(PTRef partA, PTRef partB, PTRef itp); // Verify interpolant using an external solver

    bool verifyInterpolantInternal(PTRef partA, PTRef partB, PTRef itp); // Verify interpolant internally, using OpenSMT's MainSolver

private:
    bool checkSubsetCondition(PTRef p1, PTRef p2);
};



#endif //OPENSMT_VERIFICATIONUTILS_H
