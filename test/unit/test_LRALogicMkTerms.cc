//
// Created by Martin Blicha on 02.11.18.
//

#include <gtest/gtest.h>
#include "ArithLogic.h"

class LRALogicMkTermsTest : public ::testing::Test {
protected:
    LRALogicMkTermsTest(): logic{ArithLogic::ArithType::LRA} {}
    virtual void SetUp() {
        x = logic.mkRealVar("x");
        y = logic.mkRealVar("y");
        z = logic.mkRealVar("z");
    }
    ArithLogic logic;
    PTRef x;
    PTRef y;
    PTRef z;
};

TEST_F(LRALogicMkTermsTest, test_Sum_Zero)
{
    PTRef zero = logic.mkConst("0");
    vec<PTRef> args;
    args.push(zero);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, zero);
}

TEST_F(LRALogicMkTermsTest, test_Sum_Ignore_Zeros)
{
    PTRef zero = logic.mkConst("0");
    PTRef a = logic.mkRealVar("a");
    PTRef res = logic.mkRealPlus(zero, a);

    ASSERT_EQ(res, a);
}

TEST_F(LRALogicMkTermsTest, test_One_Arg_Multiplication)
{
    PTRef two = logic.mkConst("2");
    PTRef one = logic.mkConst("1");
    PTRef a = logic.mkRealVar("a");
    PTRef div = logic.mkRealDiv(a, two);
    PTRef res = logic.mkRealTimes(div, one);

    ASSERT_EQ(res, div);
}

TEST_F(LRALogicMkTermsTest, test_Times_Ignore_Ones)
{
    PTRef one = logic.mkConst("1");
    PTRef a = logic.mkNumVar("a");
    PTRef res = logic.mkRealTimes(a, one);

    ASSERT_EQ(res, a);
}

TEST_F(LRALogicMkTermsTest, test_Times_Single_Arg)
{
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(a);
    PTRef res = logic.mkNumTimes(args);

    ASSERT_EQ(res, a);
}

TEST_F(LRALogicMkTermsTest, test_Sum_Single_Arg)
{
    PTRef a = logic.mkNumVar("a");
    vec<PTRef> args;
    args.push(a);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, a);
}

TEST_F(LRALogicMkTermsTest, test_Sum_Single_Arg_Nested)
{
    PTRef a = logic.mkNumVar("a");
    PTRef two = logic.mkConst("2");
    PTRef times = logic.mkRealTimes(a,two);
    vec<PTRef> args;
    args.push(times);
    PTRef res = logic.mkNumPlus(args);

    ASSERT_EQ(res, times);
}

TEST_F(LRALogicMkTermsTest, test_Sum_Single_Arg_Nested_With_Simplification)
{
    PTRef a = logic.mkNumVar("a");
    PTRef two = logic.mkConst("2");
    PTRef zero = logic.mkConst("0");
    PTRef times = logic.mkRealTimes(a,two);
    PTRef res = logic.mkRealPlus(times, zero);

    ASSERT_EQ(res, times);
}

TEST_F(LRALogicMkTermsTest, test_Simple_Leq)
{
    PTRef a = logic.mkNumVar("a");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkNumLeq(zero, a);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Num_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
    ASSERT_EQ(logic.getPterm(res)[1], a);
}

TEST_F(LRALogicMkTermsTest, test_Simple_Leq_Two_Vars)
{
    PTRef a = logic.mkNumVar("a");
    PTRef b = logic.mkNumVar("b");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkNumLeq(b, a);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Num_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
}

TEST_F(LRALogicMkTermsTest, test_Simple_Leq_Two_Vars2)
{
    PTRef a = logic.mkNumVar("a");
    PTRef b = logic.mkNumVar("b");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkNumLeq(a, b);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Num_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
}

TEST_F(LRALogicMkTermsTest, test_mkNumNeg)
{
    PTRef one = logic.getTerm_NumOne();
    PTRef minus = logic.mkNumNeg(one);
    ASSERT_TRUE(logic.isConstant(minus));
    ASSERT_TRUE(logic.isNegated(minus));
    ASSERT_EQ(logic.mkNumNeg(minus), one);
    ASSERT_EQ(logic.getNumConst(minus), -1);
}

TEST_F(LRALogicMkTermsTest, test_Inequality_Var_WithCoeff)
{
    PTRef a = logic.mkNumVar("a");
    PTRef minus = logic.mkNumNeg(a);
    PTRef leq = logic.mkNumLeq(minus, a);
    ASSERT_TRUE(logic.isNumLeq(leq));
    ASSERT_EQ(leq, logic.mkNumLeq(logic.getTerm_NumZero(), a));
}

TEST_F(LRALogicMkTermsTest, test_Inequality_Var_NonZero)
{
    PTRef one = logic.getTerm_NumOne();
    PTRef a = logic.mkNumVar("a");
    PTRef leq = logic.mkNumLeq(one, a);
    PTRef geq = logic.mkNumGeq(one, a);
    ASSERT_TRUE(logic.isNumLeq(leq));
    ASSERT_TRUE(logic.isNumLeq(geq));
}

TEST_F(LRALogicMkTermsTest, test_SumToZero)
{
    PTRef var = logic.mkRealVar("a");
    PTRef minusVar = logic.mkRealNeg(var);
    PTRef sum = logic.mkRealPlus(minusVar, var);
    ASSERT_EQ(sum, logic.getTerm_RealZero());
    sum = logic.mkRealPlus(var, minusVar);
    ASSERT_EQ(sum, logic.getTerm_RealZero());
}

TEST_F(LRALogicMkTermsTest, test_NonLinearException)
{
    EXPECT_THROW(logic.mkRealTimes(x,y), LANonLinearException);
    PTRef two = logic.mkConst("2");
    EXPECT_NO_THROW(logic.mkRealTimes(x,two));
}

TEST_F(LRALogicMkTermsTest, test_ConstantSimplification)
{
    PTRef two = logic.mkConst("2");
    EXPECT_EQ(logic.mkConst("1/2"), logic.mkRealDiv(logic.getTerm_NumOne(), two));
    EXPECT_EQ(two, logic.mkRealDiv(logic.mkConst("4"), two));
}

TEST_F(LRALogicMkTermsTest, test_Inequality_Constant)
{
    PTRef one = logic.getTerm_RealOne();
    PTRef a = logic.mkRealVar("a");
    PTRef sum = logic.mkRealPlus(a, one);
    ASSERT_EQ(logic.mkRealLeq(a, a), logic.getTerm_true());
    ASSERT_EQ(logic.mkRealLeq(a, sum), logic.getTerm_true());
    ASSERT_EQ(logic.mkRealGeq(a, sum), logic.getTerm_false());
}

TEST_F(LRALogicMkTermsTest, test_Inequality_Simplification)
{
    PTRef two = logic.mkConst("2");
    ASSERT_EQ(
            logic.mkRealLeq(logic.mkRealPlus(x,y), z),
            logic.mkRealLeq(
                    logic.mkRealPlus(logic.mkRealTimes(x, two), logic.mkRealTimes(y, two)),
                    logic.mkRealTimes(z, two)
            )
    );
}

TEST_F(LRALogicMkTermsTest, testAtom_LRA) {
    PTRef ineq = logic.mkNumLeq(x, logic.getTerm_NumZero());
    EXPECT_TRUE(logic.isAtom(ineq));
    EXPECT_FALSE(logic.isAtom(logic.mkNot(ineq)));

    PTRef strict = logic.mkNumLt(x, logic.getTerm_NumZero());
    EXPECT_FALSE(logic.isAtom(strict));
    EXPECT_TRUE(logic.isAtom(logic.mkNot(strict)));

    PTRef eq = logic.mkEq(x, logic.getTerm_NumZero());
    EXPECT_TRUE(logic.isAtom(eq));
    EXPECT_FALSE(logic.isAtom(logic.mkNot(eq)));

    PTRef sum = logic.mkRealPlus(x,y);
    EXPECT_FALSE(logic.isAtom(sum));
    PTRef product = logic.mkRealTimes(x, logic.mkConst(2));
    EXPECT_FALSE(logic.isAtom(product));
}

TEST_F(LRALogicMkTermsTest, test_ChainableInequality) {
    PTRef multiArgsLeq = logic.mkNumLeq({x,y,z});
    PTRef expandedLeq = logic.mkAnd(logic.mkNumLeq(x,y), logic.mkNumLeq(y,z));
    EXPECT_EQ(multiArgsLeq, expandedLeq);

    PTRef multiArgsLt = logic.mkNumLt({x,y,z});
    PTRef expandedLt = logic.mkAnd(logic.mkNumLt(x,y), logic.mkNumLt(y,z));
    EXPECT_EQ(multiArgsLt, expandedLt);

    PTRef multiArgsGeq = logic.mkNumGeq({x,y,z});
    PTRef expandedGeq = logic.mkAnd(logic.mkNumGeq(x,y), logic.mkNumGeq(y,z));
    EXPECT_EQ(multiArgsGeq, expandedGeq);

    PTRef multiArgsGt = logic.mkNumGt({x,y,z});
    PTRef expandedGt = logic.mkAnd(logic.mkNumGt(x,y), logic.mkNumGt(y,z));
    EXPECT_EQ(multiArgsGt, expandedGt);
}

TEST_F(LRALogicMkTermsTest, test_EqualityNormalization) {
    PTRef two = logic.mkConst(2);
    PTRef eq1 = logic.mkEq(x, y);
    PTRef eq2 = logic.mkEq(logic.mkNumTimes(x, two), logic.mkNumTimes(y, two));
//    std::cout << logic.printTerm(eq1) << std::endl;
//    std::cout << logic.printTerm(eq2) << std::endl;
    EXPECT_EQ(eq1, eq2);
}

TEST_F(LRALogicMkTermsTest, test_EqualityNormalization_ToConstantExpression) {
    PTRef two = logic.mkConst(2);
    PTRef eq1 = logic.mkEq(x, logic.mkNumPlus(x, two));
    EXPECT_EQ(eq1, logic.getTerm_false());
}
