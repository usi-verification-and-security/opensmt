//
// Created by Antti on 31.03.20.
//
#include <gtest/gtest.h>
#include <Logic.h>
#include <SMTConfig.h>

class LogicMkTermsTest: public ::testing::Test {
public:
    LogicMkTermsTest() {}
};

TEST_F(LogicMkTermsTest, test_Distinct){
    SMTConfig config;
    Logic logic{config};

    SRef ufsort = logic.declareSort("U", nullptr);
    PTRef x = logic.mkVar(ufsort, "x");
    PTRef y = logic.mkVar(ufsort, "y");
    vec<PTRef> args;
    args.push(x);
    args.push(y);
    PTRef distinct = logic.mkDistinct(args);
    ASSERT_NE(distinct, logic.getTerm_false());
    ASSERT_NE(distinct, logic.getTerm_true());

    args.clear();
    args.push(x);
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_true());

    args.clear();
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_true());

    args.push(x);
    args.push(x);
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_false());

    args.clear();
    args.push(x);
    args.push(y);
    args.push(x);
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_false());

    PTRef b1 = logic.mkBoolVar("b1");
    PTRef b2 = logic.mkBoolVar("b2");

    args.clear();
    args.push(b1);
    args.push(b2);
    distinct = logic.mkDistinct(args);
    ASSERT_TRUE(logic.isXor(distinct));

    PTRef b3 = logic.mkBoolVar("b3");
    args.push(b3);
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_false());
}
