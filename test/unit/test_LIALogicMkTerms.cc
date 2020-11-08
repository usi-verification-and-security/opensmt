//
// Created by prova on 11.09.20.
//

#include <gtest/gtest.h>
#include <LIALogic.h>

class LIALogicMkTermsTest: public ::testing::Test {
public:
    LIALogic logic;
    LIALogicMkTermsTest(): logic{} {}
};

TEST_F(LIALogicMkTermsTest, testIsNumTerm) {
    PTRef c = logic.mkBoolVar("c");
    ASSERT_FALSE(logic.isNumTerm(c));
    PTRef t = logic.mkNumVar("t");
    ASSERT_TRUE(logic.isNumTerm(t));
    PTRef e = logic.mkNumTimes(logic.mkNumVar("e"), logic.mkConst(-114));
    ASSERT_TRUE(logic.isNumTerm(e));
    PTRef ite = logic.mkIte(c, t, e);
    ASSERT_TRUE(logic.isNumTerm(ite));
    PTRef ite_term = logic.mkNumTimes(ite, logic.mkConst(14));
    ASSERT_TRUE(logic.isNumTerm(ite_term));

    PTRef sum = logic.mkNumPlus(t, e);
    ASSERT_FALSE(logic.isNumTerm(sum));
}

TEST_F(LIALogicMkTermsTest, testDeepLessThan) {
    PTRef x = logic.mkNumVar("x");
    PTRef a = logic.mkConst(3);
    PTRef y = logic.mkNumVar("y");
    PTRef b = logic.mkConst(-4);
    PTRef prod2 = logic.mkNumTimes(y, b);
    PTRef prod1 = logic.mkNumTimes(x, a);

    LessThan_deepPTRef lt_deep(&logic);
    ASSERT_EQ(lt_deep(prod1, prod2), lt_deep(x, y));
//    LessThan_PTRef lt_shallow;
//    ASSERT_NE(lt_shallow(prod1, prod2), lt_shallow(x, y));
}
