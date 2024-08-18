/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include <tsolvers/lasolver/LASolver.h>

namespace opensmt {

class LASolverIncrementalityTest : public ::testing::Test {
public:
    LASolverIncrementalityTest() : logic(Logic_t::QF_LRA), solver(c, logic) {}
    SMTConfig c;
    ArithLogic logic;
    LASolver solver;
};

TEST_F(LASolverIncrementalityTest, test_Incrementality) {

    // x >= 1
    PTRef c1 = logic.getTerm_RealOne();
    PTRef x = logic.mkRealVar("x");
    PTRef constr1 = logic.mkGeq(x, c1);
    solver.declareAtom(constr1);
    solver.assertLit({constr1, l_True});
    auto res = solver.check(true);
    ASSERT_EQ(res, TRes::SAT);

    // 0 <= -y - x
    PTRef y = logic.mkRealVar("y");
    PTRef p1 = logic.mkMinus(logic.mkNeg(y), x);
    PTRef constr3 = logic.mkLeq(logic.getTerm_RealZero(), p1);
    solver.declareAtom(constr3);
    solver.assertLit({constr3, l_True});
    res = solver.check(true);
    ASSERT_EQ(res, TRes::SAT);

    // y >= 1
    PTRef constr2 = logic.mkGeq(y, c1);
    solver.declareAtom(constr2);
    solver.assertLit({constr2, l_True});
    res = solver.check(true);
    ASSERT_EQ(res, TRes::UNSAT);
}

}
