/*
 * Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include <opensmt/opensmt2.h>

using namespace opensmt;

void usingWrapper();
void creatingComponentsDirectly();

int main()
{
    // There are now two ways to construct the necessary objects
    // 1. Using a provided wrapper
    usingWrapper();
    // 2. Creating the necessary components directly
    creatingComponentsDirectly();
    return 0;

}

void usingWrapper() {
    Opensmt osmt(qf_alia, "OpenSMT");
    MainSolver & mainSolver = osmt.getMainSolver();
    // You can ask the wrapper for the concrete subclass of Logic, but YOU need to make sure it matches the type you
    // have provided in the constructor
    ArithLogic & logic = osmt.getLIALogic();

    SRef int2intSort = logic.getArraySort(logic.getSort_int(), logic.getSort_int());
    PTRef zero = logic.getTerm_IntZero();
    PTRef one = logic.getTerm_IntOne();
    PTRef a = logic.mkVar(int2intSort, "a");
    // assertion a<0 -> 1>[0] = 1
    PTRef store = logic.mkStore({a, zero, one});
    PTRef select = logic.mkSelect({store, zero});
    PTRef eq = logic.mkEq(select, one);
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
    ArithLogic logic{Logic_t::QF_ALIA};
    SMTConfig config;
    MainSolver mainSolver(logic, config, "ALIA solver");

    SRef int2intSort = logic.getArraySort(logic.getSort_int(), logic.getSort_int());
    // check that two arrays can be different
    PTRef a = logic.mkVar(int2intSort, "a");
    PTRef b = logic.mkVar(int2intSort, "b");
    PTRef eq = logic.mkEq(a, b);
    mainSolver.insertFormula(logic.mkNot(eq));
    sstat r = mainSolver.check();
    assert(r == s_True);
    // TODO: print model

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
