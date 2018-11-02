//
// Created by Martin Blicha on 02.11.18.
//

#include <gtest/gtest.h>
#include "LRALogic.h"

TEST(ArithmeticExpressions_test, test_Sum_Zero)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef zero = logic.mkConst("0");
    vec<PTRef> args;
    args.push(zero);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, zero);
}

TEST(ArithmeticExpressions_test, test_Sum_Ignore_Zeros)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef zero = logic.mkConst("0");
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(zero);
    args.push(a);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, a);
}

TEST(ArithmeticExpressions_test, test_One_Arg_Multiplication)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef zero = logic.mkConst("0");
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

TEST(ArithmeticExpressions_test, test_Times_Ignore_Ones)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef one = logic.mkConst("1");
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(a);
    args.push(one);
    PTRef res = logic.mkNumTimes(args);

    ASSERT_EQ(res, a);
}

TEST(ArithmeticExpressions_test, test_Times_Single_Arg)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(a);
    PTRef res = logic.mkNumTimes(args);

    ASSERT_EQ(res, a);
}

TEST(ArithmeticExpressions_test, test_Sum_Single_Arg)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(a);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, a);
}

TEST(ArithmeticExpressions_test, test_Sum_Single_Arg_Nested)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef a = logic.mkNumVar("a");
    PTRef two = logic.mkConst("2");
    PTRef zero = logic.mkConst("0");
    PTRef times = logic.mkNumTimes(a,two);
    vec<PTRef> args;
    args.push(times);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, times);
}

TEST(ArithmeticExpressions_test, test_Sum_Single_Arg_Nested_With_Simplification)
{
    SMTConfig config;
    LRALogic logic{config};
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

TEST(ArithmeticExpressions_test, test_Simple_Leq)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef a = logic.mkNumVar("a");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkNumLeq(zero, a);
    const Pterm& term = logic.getPterm(res);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Num_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
    ASSERT_EQ(logic.getPterm(res)[1], a);
}

TEST(ArithmeticExpressions_test, test_Simple_Leq_Two_Vars)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef a = logic.mkNumVar("a");
    PTRef b = logic.mkNumVar("b");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkNumLeq(b, a);
    const Pterm& term = logic.getPterm(res);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Num_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
}

TEST(ArithmeticExpressions_test, test_Simple_Leq_Two_Vars2)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef a = logic.mkNumVar("a");
    PTRef b = logic.mkNumVar("b");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkNumLeq(a, b);
    const Pterm& term = logic.getPterm(res);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Num_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
}

TEST(ArithmeticExpressions_test, test_mkNumNeg)
{
    SMTConfig config;
    LRALogic logic{config};
    PTRef one = logic.getTerm_NumOne();
    PTRef minus = logic.mkNumNeg(one);
    ASSERT_TRUE(logic.isConstant(minus));
    ASSERT_TRUE(logic.isNegated(minus));
    ASSERT_EQ(logic.mkNumNeg(minus), one);
    ASSERT_EQ(logic.getNumConst(minus), -1);
}



