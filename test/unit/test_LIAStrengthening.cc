//
// Created by prova on 30.09.20.
//
#include <gtest/gtest.h>
#include <common/numbers/Real.h>
#include <logics/ArithLogic.h>

namespace opensmt {

class LIAStrengthening: public ::testing::Test {
public:
    ArithLogic logic;
    LIAStrengthening() : logic{Logic_t::QF_LIA} {}
};

TEST_F(LIAStrengthening, test_LIAStrengthening) {
    PTRef c2 = logic.mkIntConst(2);
    PTRef c3 = logic.mkIntConst(3);
    PTRef x = logic.mkIntVar("x");
    PTRef y = logic.mkIntVar("y");
    PTRef sum = logic.mkTimes(c2, logic.mkPlus(x, y));
    PTRef ineq = logic.mkGeq(sum, c3);
    ASSERT_EQ(logic.getConstantFromLeq(ineq), logic.mkConst("2"));
    ASSERT_EQ(logic.getTermFromLeq(ineq), logic.mkPlus(x,y));
}

}
