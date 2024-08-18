//
// Created by Martin Blicha on 02.11.18.
//

#include <gtest/gtest.h>
#include <logics/ArithLogic.h>

namespace opensmt {

class LRALogicMkTermsTest : public ::testing::Test {
protected:
    LRALogicMkTermsTest(): logic{Logic_t::QF_LRA} {}
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
    PTRef res = logic.mkPlus(args);

    ASSERT_EQ(res, zero);
}

TEST_F(LRALogicMkTermsTest, test_Sum_Ignore_Zeros)
{
    PTRef zero = logic.mkConst("0");
    PTRef a = logic.mkRealVar("a");
    PTRef res = logic.mkPlus(zero, a);

    ASSERT_EQ(res, a);
}

TEST_F(LRALogicMkTermsTest, test_One_Arg_Multiplication)
{
    PTRef two = logic.mkConst("2");
    PTRef one = logic.mkConst("1");
    PTRef a = logic.mkRealVar("a");
    PTRef div = logic.mkRealDiv(a, two);
    PTRef res = logic.mkTimes(div, one);

    ASSERT_EQ(res, div);
}

TEST_F(LRALogicMkTermsTest, test_Times_Ignore_Ones)
{
    PTRef one = logic.mkConst("1");
    PTRef a = logic.mkRealVar("a");
    PTRef res = logic.mkTimes(a, one);

    ASSERT_EQ(res, a);
}

TEST_F(LRALogicMkTermsTest, test_Times_Single_Arg)
{
    PTRef a = logic.mkRealVar("a");
    vec<PTRef> args;
    args.push(a);
    PTRef res = logic.mkTimes(args);

    ASSERT_EQ(res, a);
}

TEST_F(LRALogicMkTermsTest, test_Sum_Single_Arg)
{
    PTRef a = logic.mkRealVar("a");
    vec<PTRef> args;
    args.push(a);
    PTRef res = logic.mkPlus(args);

    ASSERT_EQ(res, a);
}

TEST_F(LRALogicMkTermsTest, test_Sum_Single_Arg_Nested)
{
    PTRef a = logic.mkRealVar("a");
    PTRef two = logic.mkConst("2");
    PTRef times = logic.mkTimes(a,two);
    vec<PTRef> args;
    args.push(times);
    PTRef res = logic.mkPlus(args);

    ASSERT_EQ(res, times);
}

TEST_F(LRALogicMkTermsTest, test_Sum_Single_Arg_Nested_With_Simplification)
{
    PTRef a = logic.mkRealVar("a");
    PTRef two = logic.mkConst("2");
    PTRef zero = logic.mkConst("0");
    PTRef times = logic.mkTimes(a,two);
    PTRef res = logic.mkPlus(times, zero);

    ASSERT_EQ(res, times);
}

TEST_F(LRALogicMkTermsTest, test_Simple_Leq)
{
    PTRef a = logic.mkRealVar("a");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkLeq(zero, a);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Real_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
    ASSERT_EQ(logic.getPterm(res)[1], a);
}

TEST_F(LRALogicMkTermsTest, test_Simple_Leq_Two_Vars)
{
    PTRef a = logic.mkRealVar("a");
    PTRef b = logic.mkRealVar("b");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkLeq(b, a);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Real_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
}

TEST_F(LRALogicMkTermsTest, test_Simple_Leq_Two_Vars2)
{
    PTRef a = logic.mkRealVar("a");
    PTRef b = logic.mkRealVar("b");
    PTRef zero = logic.mkConst("0");
    PTRef res = logic.mkLeq(a, b);
    ASSERT_EQ(logic.getSymRef(res),logic.get_sym_Real_LEQ());
    ASSERT_EQ(logic.getPterm(res)[0], zero);
}

TEST_F(LRALogicMkTermsTest, test_mkNumNeg)
{
    PTRef one = logic.getTerm_RealOne();
    PTRef minus = logic.mkNeg(one);
    ASSERT_TRUE(logic.isConstant(minus));
    ASSERT_TRUE(logic.isNumConst(minus));
    ASSERT_LT(logic.getNumConst(minus), 0);
    ASSERT_EQ(logic.mkNeg(minus), one);
    ASSERT_EQ(logic.getNumConst(minus), -1);
}

TEST_F(LRALogicMkTermsTest, test_Inequality_Var_WithCoeff)
{
    PTRef a = logic.mkRealVar("a");
    PTRef minus = logic.mkNeg(a);
    PTRef leq = logic.mkLeq(minus, a);
    ASSERT_TRUE(logic.isLeq(leq));
    ASSERT_EQ(leq, logic.mkLeq(logic.getTerm_RealZero(), a));
}

TEST_F(LRALogicMkTermsTest, test_Inequality_Var_NonZero)
{
    PTRef one = logic.getTerm_RealOne();
    PTRef a = logic.mkRealVar("a");
    PTRef leq = logic.mkLeq(one, a);
    PTRef geq = logic.mkGeq(one, a);
    ASSERT_TRUE(logic.isLeq(leq));
    ASSERT_TRUE(logic.isLeq(geq));
}

TEST_F(LRALogicMkTermsTest, test_SumToZero)
{
    PTRef var = logic.mkRealVar("a");
    PTRef minusVar = logic.mkNeg(var);
    PTRef sum = logic.mkPlus(minusVar, var);
    ASSERT_EQ(sum, logic.getTerm_RealZero());
    sum = logic.mkPlus(var, minusVar);
    ASSERT_EQ(sum, logic.getTerm_RealZero());
}

TEST_F(LRALogicMkTermsTest, test_NonLinearException)
{
    EXPECT_THROW(logic.mkTimes(x,y), LANonLinearException);
    PTRef two = logic.mkConst("2");
    EXPECT_NO_THROW(logic.mkTimes(x,two));
}

TEST_F(LRALogicMkTermsTest, test_ConstantSimplification)
{
    PTRef two = logic.mkConst("2");
    EXPECT_EQ(logic.mkConst("1/2"), logic.mkRealDiv(logic.getTerm_RealOne(), two));
    EXPECT_EQ(two, logic.mkRealDiv(logic.mkConst("4"), two));
}

TEST_F(LRALogicMkTermsTest, test_Inequality_Constant)
{
    PTRef one = logic.getTerm_RealOne();
    PTRef a = logic.mkRealVar("a");
    PTRef sum = logic.mkPlus(a, one);
    ASSERT_EQ(logic.mkLeq(a, a), logic.getTerm_true());
    ASSERT_EQ(logic.mkLeq(a, sum), logic.getTerm_true());
    ASSERT_EQ(logic.mkGeq(a, sum), logic.getTerm_false());
}

TEST_F(LRALogicMkTermsTest, test_Inequality_Simplification)
{
    PTRef two = logic.mkConst("2");
    ASSERT_EQ(
            logic.mkLeq(logic.mkPlus(x,y), z),
            logic.mkLeq(
                    logic.mkPlus(logic.mkTimes(x, two), logic.mkTimes(y, two)),
                    logic.mkTimes(z, two)
            )
    );
}

TEST_F(LRALogicMkTermsTest, testAtom_LRA) {
    PTRef ineq = logic.mkLeq(x, logic.getTerm_RealZero());
    EXPECT_TRUE(logic.isAtom(ineq));
    EXPECT_FALSE(logic.isAtom(logic.mkNot(ineq)));

    PTRef strict = logic.mkLt(x, logic.getTerm_RealZero());
    EXPECT_FALSE(logic.isAtom(strict));
    EXPECT_TRUE(logic.isAtom(logic.mkNot(strict)));

    PTRef eq = logic.mkEq(x, logic.getTerm_RealZero());
    EXPECT_TRUE(logic.isAtom(eq));
    EXPECT_FALSE(logic.isAtom(logic.mkNot(eq)));

    PTRef sum = logic.mkPlus(x,y);
    EXPECT_FALSE(logic.isAtom(sum));
    PTRef product = logic.mkTimes(x, logic.mkRealConst(2));
    EXPECT_FALSE(logic.isAtom(product));
}

TEST_F(LRALogicMkTermsTest, test_ChainableInequality) {
    PTRef multiArgsLeq = logic.mkLeq({x,y,z});
    PTRef expandedLeq = logic.mkAnd(logic.mkLeq(x,y), logic.mkLeq(y,z));
    EXPECT_EQ(multiArgsLeq, expandedLeq);

    PTRef multiArgsLt = logic.mkLt({x,y,z});
    PTRef expandedLt = logic.mkAnd(logic.mkLt(x,y), logic.mkLt(y,z));
    EXPECT_EQ(multiArgsLt, expandedLt);

    PTRef multiArgsGeq = logic.mkGeq({x,y,z});
    PTRef expandedGeq = logic.mkAnd(logic.mkGeq(x,y), logic.mkGeq(y,z));
    EXPECT_EQ(multiArgsGeq, expandedGeq);

    PTRef multiArgsGt = logic.mkGt({x,y,z});
    PTRef expandedGt = logic.mkAnd(logic.mkGt(x,y), logic.mkGt(y,z));
    EXPECT_EQ(multiArgsGt, expandedGt);
}

TEST_F(LRALogicMkTermsTest, test_EqualityNormalization_Commutativity) {
    PTRef two = logic.mkRealConst(2);
    PTRef eq1 = logic.mkEq(x, two);
    PTRef eq2 = logic.mkEq(two, x);
    ASSERT_EQ(eq1, eq2);
}

TEST_F(LRALogicMkTermsTest, test_EqualityNormalization) {
    PTRef two = logic.mkRealConst(2);
    PTRef eq1 = logic.mkEq(x, y);
    PTRef eq2 = logic.mkEq(logic.mkTimes(x, two), logic.mkTimes(y, two));
//    std::cout << logic.printTerm(eq1) << std::endl;
//    std::cout << logic.printTerm(eq2) << std::endl;
    EXPECT_EQ(eq1, eq2);
}

TEST_F(LRALogicMkTermsTest, test_EqualityNormalization_ToConstantExpression) {
    PTRef two = logic.mkRealConst(2);
    PTRef eq1 = logic.mkEq(x, logic.mkPlus(x, two));
    EXPECT_EQ(eq1, logic.getTerm_false());
}

TEST_F(LRALogicMkTermsTest, test_FailWithIntArgs) {
    EXPECT_THROW(logic.mkIntConst(2), ApiException);
}

}
