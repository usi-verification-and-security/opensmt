//
// Created by prova on 30.09.20.
//
#include <gtest/gtest.h>
#include <Real.h>
#include <stdlib.h>
#include <Vec.h>
#include <Sort.h>
#include <SMTConfig.h>
#include <ArithLogic.h>

class LIAStrengthening: public ::testing::Test {
public:
    ArithLogic logic;
    LIAStrengthening() : logic{ArithLogic::ArithType::LIA} {}
};

TEST_F(LIAStrengthening, test_LIAStrengthening) {
    PTRef c2 = logic.mkConst(2);
    PTRef c3 = logic.mkConst(3);
    PTRef x = logic.mkIntVar("x");
    PTRef y = logic.mkIntVar("y");
    PTRef sum = logic.mkIntTimes(c2, logic.mkIntPlus(x, y));
    PTRef ineq = logic.mkIntGeq(sum, c3);
    ASSERT_EQ(logic.getConstantFromLeq(ineq), logic.mkConst("2"));
    ASSERT_EQ(logic.getTermFromLeq(ineq), logic.mkIntPlus(x,y));
}
