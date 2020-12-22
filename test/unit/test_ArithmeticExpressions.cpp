//
// Created by Martin Blicha on 02.11.18.
//

#include <gtest/gtest.h>
#include "LRALogic.h"
#include "FastRational.h"

class ArithmeticExpressions_test : public ::testing::Test {
protected:
    ArithmeticExpressions_test(): logic{} {}
    virtual void SetUp() {
        x = logic.mkNumVar("x");
        y = logic.mkNumVar("y");
        z = logic.mkNumVar("z");
    }
    LRALogic logic;
    PTRef x;
    PTRef y;
    PTRef z;
};

TEST_F(ArithmeticExpressions_test, test_Sum_Zero)
{
    PTRef zero = logic.mkConst("0");
    vec<PTRef> args;
    args.push(zero);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, zero);
}

TEST_F(ArithmeticExpressions_test, test_Sum_Ignore_Zeros)
{
    PTRef zero = logic.mkConst("0");
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(zero);
    args.push(a);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, a);
}

TEST_F(ArithmeticExpressions_test, test_One_Arg_Multiplication)
{
    PTRef two = logic.mkConst("2");
    PTRef one = logic.mkConst("1");
    PTRef a = logic.mkNumVar("a");
    PTRef div = logic.mkNumDiv(a, two);
    vec<PTRef> args;
    args.push(div);
    args.push(one);
    PTRef res = logic.mkNumTimes(args);

    ASSERT_EQ(res, div);
}

TEST_F(ArithmeticExpressions_test, test_Times_Ignore_Ones)
{
    PTRef one = logic.mkConst("1");
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(a);
    args.push(one);
    PTRef res = logic.mkNumTimes(args);

    ASSERT_EQ(res, a);
}

TEST_F(ArithmeticExpressions_test, test_Times_Single_Arg)
{
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(a);
    PTRef res = logic.mkNumTimes(args);

    ASSERT_EQ(res, a);
}

TEST_F(ArithmeticExpressions_test, test_Sum_Single_Arg)
{
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(a);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, a);
}

TEST_F(ArithmeticExpressions_test, test_Sum_Single_Arg_Nested)
{
    PTRef a = logic.mkNumVar("a");
    PTRef two = logic.mkConst("2");
    PTRef times = logic.mkNumTimes(a,two);
    vec<PTRef> args;
    args.push(times);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, times);
}

TEST_F(ArithmeticExpressions_test, test_Sum_Single_Arg_Nested_With_Simplification)
{
    PTRef a = logic.mkNumVar("a");
    PTRef two = logic.mkConst("2");
    PTRef zero = logic.mkConst("0");
    PTRef times = logic.mkNumTimes(a,two);
    vec<PTRef> args;
    args.push(times);
    args.push(zero);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, times);
}

TEST_F(ArithmeticExpressions_test, test_Simple_Leq)
{
    PTRef a = logic.mkNumVar("a");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkNumLeq(zero, a);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Num_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
    ASSERT_EQ(logic.getPterm(res)[1], a);
}

TEST_F(ArithmeticExpressions_test, test_Simple_Leq_Two_Vars)
{
    PTRef a = logic.mkNumVar("a");
    PTRef b = logic.mkNumVar("b");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkNumLeq(b, a);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Num_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
}

TEST_F(ArithmeticExpressions_test, test_Simple_Leq_Two_Vars2)
{
    PTRef a = logic.mkNumVar("a");
    PTRef b = logic.mkNumVar("b");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkNumLeq(a, b);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Num_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
}

TEST_F(ArithmeticExpressions_test, test_mkNumNeg)
{
    PTRef one = logic.getTerm_NumOne();
    PTRef minus = logic.mkNumNeg(one);
    ASSERT_TRUE(logic.isConstant(minus));
    ASSERT_TRUE(logic.isNegated(minus));
    ASSERT_EQ(logic.mkNumNeg(minus), one);
    ASSERT_EQ(logic.getNumConst(minus), -1);
}

TEST_F(ArithmeticExpressions_test, test_Inequality_Var_WithCoeff)
{
    PTRef a = logic.mkNumVar("a");
    PTRef minus = logic.mkNumNeg(a);
    PTRef leq = logic.mkNumLeq(minus, a);
    ASSERT_TRUE(logic.isNumLeq(leq));
    ASSERT_EQ(leq, logic.mkNumLeq(logic.getTerm_NumZero(), a));
}

TEST_F(ArithmeticExpressions_test, test_Inequality_Var_NonZero)
{
    PTRef one = logic.getTerm_NumOne();
    PTRef a = logic.mkNumVar("a");
    PTRef leq = logic.mkNumLeq(one, a);
    PTRef geq = logic.mkNumGeq(one, a);
    ASSERT_TRUE(logic.isNumLeq(leq));
    ASSERT_TRUE(logic.isNumLeq(geq));
}

TEST_F(ArithmeticExpressions_test, test_SumToZero)
{
    PTRef var = logic.mkNumVar("a");
    PTRef minusVar = logic.mkNumNeg(var);
    vec<PTRef> args;
    args.push(minusVar);
    args.push(var);
    PTRef sum = logic.mkNumPlus(args);
    ASSERT_EQ(sum, logic.getTerm_NumZero());
    args.clear();
    args.push(var);
    args.push(minusVar);
    sum = logic.mkNumPlus(args);
    ASSERT_EQ(sum, logic.getTerm_NumZero());
}

TEST_F(ArithmeticExpressions_test, test_NonLinearException)
{
    EXPECT_THROW(logic.mkNumTimes(x,y), LANonLinearException);
    PTRef two = logic.mkConst("2");
    EXPECT_NO_THROW(logic.mkNumTimes(x,two));
}

TEST_F(ArithmeticExpressions_test, test_Inequality_Constant)
{
    PTRef one = logic.getTerm_NumOne();
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(a);
    args.push(one);
    PTRef sum = logic.mkNumPlus(args);
    ASSERT_EQ(logic.mkNumLeq(a, a), logic.getTerm_true());
    ASSERT_EQ(logic.mkNumLeq(a, sum), logic.getTerm_true());
    ASSERT_EQ(logic.mkNumGeq(a, sum), logic.getTerm_false());
}

