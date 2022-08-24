/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include <lasolver/LASolver.h>

class LASolverIncrementalityTest : public ::testing::Test {
public:
    LASolverIncrementalityTest() : logic(opensmt::Logic_t::QF_LRA), solver(c, logic) {}
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


TEST_F(LASolverIncrementalityTest, test_Propagation) {

    // x >= 1
    PTRef c1 = logic.getTerm_RealOne();
    PTRef x = logic.mkRealVar("x");
    PTRef constr1 = logic.mkGeq(x, c1);
    solver.declareAtom(constr1);
    solver.assertLit({constr1, l_True});
    auto rest = solver.check(true);
    ASSERT_EQ(rest, TRes::SAT);


    // x <= 10
    PTRef c2 = logic.mkRealConst(10);
    PTRef constr2 = logic.mkLeq(x, c2);
    solver.declareAtom(constr2);

    // x <= 7
    PTRef c3 = logic.mkRealConst(7);
    PTRef constr3 = logic.mkLeq(x, c3);
    solver.declareAtom(constr3);

    // x >= 2
    PTRef c4 = logic.mkRealConst(2);
    PTRef constr4 = logic.mkGeq(x, c4);
    solver.declareAtom(constr4);

    PtAsgn prLit1 = PtAsgn(constr3, l_True);
    bool res = solver.wouldDeduce(prLit1);
    ASSERT_EQ(res, true);

    PtAsgn prLit2 = PtAsgn(constr3, l_False);
    res = solver.wouldDeduce(prLit2);
    ASSERT_EQ(res, true);

    PtAsgn prLit3 = PtAsgn(constr2, l_True);
    res = solver.wouldDeduce(prLit3);
    ASSERT_EQ(res, false);

    PtAsgn prLit4 = PtAsgn(constr4, l_True);
    res = solver.wouldDeduce(prLit4);
    ASSERT_EQ(res, false);

    PtAsgn prLit5 = PtAsgn(constr4, l_False);
    res = solver.wouldDeduce(prLit5);
    ASSERT_EQ(res, true);
}