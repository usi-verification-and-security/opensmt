//
// Created by prova on 30.09.20.
//
#include <gtest/gtest.h>
#include <Real.h>
#include <stdlib.h>
#include <Vec.h>
#include <Sort.h>
#include <SMTConfig.h>
#include <LIALogic.h>

class LIAStrengthening: public ::testing::Test {
public:
    LIALogic logic;
    LIAStrengthening() : logic{} {}
};

TEST_F(LIAStrengthening, test_LIAStrengthening) {
    PTRef c2 = logic.mkConst(2);
    PTRef c3 = logic.mkConst(3);
    PTRef x = logic.mkNumVar("x");
    PTRef y = logic.mkNumVar("y");
    PTRef sum = logic.mkNumTimes(c2, logic.mkNumPlus(x, y));
    PTRef ineq = logic.mkNumGeq(sum, c3);
    ASSERT_EQ(logic.getConstantFromLeq(ineq), logic.mkConst("2"));
    ASSERT_EQ(logic.getTermFromLeq(ineq), logic.mkNumPlus(x,y));
}
