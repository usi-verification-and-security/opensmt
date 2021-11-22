//
// Created by Martin Blicha on 29.07.20.
//

#include <opensmt/opensmt2.h>
#include <stdio.h>

void usingWrapper();
void creatingComponentsDirectly();

int
main(int argc, char** argv)
{
    // There are now two ways to construct the necessary objects
    // 1. Using a provided wrapper
    usingWrapper();
    // 2. Creating the necessary components directly
    creatingComponentsDirectly();
    return 0;

}

void usingWrapper() {
    Opensmt* osmt = new Opensmt(qf_lia, "OpenSMT");
    SMTConfig& c = osmt->getConfig();
    MainSolver& mainSolver = osmt->getMainSolver();
    // You can ask the wrapper for the concrete subclass of Logic, but YOU need to make sure it matches the type you
    // have provided in the constructor
    auto & logic = osmt->getLIALogic();

    // Create the constant
    PTRef cons = logic.mkIntConst(-1);
    PTRef x = logic.mkIntVar("x");
    PTRef y = logic.mkIntVar("y");
    // assertion x + y = y + x
    PTRef lhs = logic.mkPlus(x, y);
    PTRef rhs = logic.mkPlus(y, x);
    PTRef eq = logic.mkEq(lhs, rhs);
    // test if the negation is satisfiable
    mainSolver.insertFormula(logic.mkNot(eq));
    sstat r = mainSolver.check();
    assert(r == s_False);

    if (r == s_True)
        printf("sat\n");
    else if (r == s_False)
    {
        printf("unsat\n");
    }
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");
}

void creatingComponentsDirectly() {
    ArithLogic logic{opensmt::Logic_t::QF_LIA};
    SMTConfig config;
    MainSolver mainSolver(logic, config, "LIA solver");

    // Create the constant
    PTRef cons = logic.mkIntConst(-1);
    PTRef x = logic.mkIntVar("x");
    PTRef y = logic.mkIntVar("y");
    // assertion x + y = y + x
    PTRef lhs = logic.mkPlus(x, y);
    PTRef rhs = logic.mkPlus(y, x);
    PTRef eq = logic.mkEq(lhs, rhs);
    // test if the negation is satisfiable
    mainSolver.insertFormula(logic.mkNot(eq));
    sstat r = mainSolver.check();
    assert(r == s_False);

    if (r == s_True)
        printf("sat\n");
    else if (r == s_False)
    {
        printf("unsat\n");
    }
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");
}


