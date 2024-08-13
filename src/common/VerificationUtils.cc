/*
 *  Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "VerificationUtils.h"

#include <api/MainSolver.h>
#include <common/TreeOps.h>

namespace opensmt {
bool VerificationUtils::verifyInterpolantInternal(PTRef Apartition, PTRef Bpartition, PTRef itp) {
    SMTConfig validationConfig;
    MainSolver validationSolver(logic, validationConfig, "validator");
    //    std::cout << "A part:   " << logic.printTerm(Apartition) << '\n';
    //    std::cout << "B part:   " << logic.printTerm(Bpartition) << '\n';
    //    std::cout << "Interpol: " << logic.printTerm(itp) << std::endl;
    validationSolver.push();
    validationSolver.insertFormula(logic.mkNot(logic.mkImpl(Apartition, itp)));
    auto res = validationSolver.check();
    bool ok = res == s_False;
    if (not ok) { return false; }
    validationSolver.pop();
    validationSolver.insertFormula(logic.mkNot(logic.mkImpl(itp, logic.mkNot(Bpartition))));
    res = validationSolver.check();
    ok = res == s_False;
    if (not ok) { return false; }
    return checkSubsetCondition(itp, Apartition) and checkSubsetCondition(itp, Bpartition);
}

bool VerificationUtils::checkSubsetCondition(PTRef p1, PTRef p2) const {
    auto vars_p1 = variables(logic, p1);
    auto vars_p2 = variables(logic, p2);
    for (PTRef key : vars_p1) {
        if (std::find(vars_p2.begin(), vars_p2.end(), key) == vars_p2.end()) { return false; }
    }
    return true;
}

bool VerificationUtils::impliesInternal(PTRef antecedent, PTRef consequent) {
    SMTConfig validationConfig;
    MainSolver validationSolver(logic, validationConfig, "validator");
    validationSolver.insertFormula(logic.mkNot(logic.mkImpl(antecedent, consequent)));
    auto res = validationSolver.check();
    bool valid = res == s_False;
    return valid;
}
} // namespace opensmt
