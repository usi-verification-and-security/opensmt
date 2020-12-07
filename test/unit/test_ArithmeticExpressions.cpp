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

TEST_F(ArithmeticExpressions_test, test_creation)
{
    {
        // a = INT_MIN / INT_MAX is the number that has the smallest nominator and biggest denominator such that it still fits the word representation
        FastRational a(INT_MIN, INT_MAX);
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_EQ(a, FastRational("-2147483648/2147483647"));
    }
    {
        // a = INT_MAX / INT_MAX = 1 but in current implementation handles big values.
        FastRational a(INT_MAX,INT_MAX);
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_EQ(a, 1);
    }
}

TEST_F(ArithmeticExpressions_test, test_addition)
{
    {
        // b.num == 0
        FastRational a(1, 3);
        FastRational b(0);
        ASSERT_EQ(a + b, FastRational(1, 3));
        ASSERT_EQ(-a + b, FastRational(-1, 3));
    }

    {
        // a.num == 0
        FastRational a(0);
        FastRational b(1, 3);
        ASSERT_EQ(a + b, FastRational(1, 3));
        ASSERT_EQ(a + (-b), FastRational(-1, 3));
    }

    {
        // a == -b
        FastRational a(1,3);
        FastRational b(-1,3);
        ASSERT_EQ(a+b, 0);
    }

    {
        // b.den == 1
        // result fits in word
        FastRational a(1,3);
        FastRational b(1);
        ASSERT_EQ(a+b, FastRational(4,3));
    }
    {
        // b.den == 1
        // a.num + b.num*a.den does not fit in word (but fits by definition in lword)
        // (a.num + b.num*a.den) / gcd(a.num+b.num*a.den, a.den) does not fit in word
        FastRational a(INT_MAX,UINT_MAX);
        FastRational b(INT_MAX);
        FastRational sum = a+b;
        ASSERT_EQ(sum, FastRational("9223372032559808512/4294967295"));
        ASSERT_FALSE(sum.wordPartValid());
    }
    {
        // b.den == 1
        // a and b negative
        // a.num + b.num*a.den does not fit in word (but fits by definition in lword)
        // (a.num + b.num*a.den) / gcd(a.num+b.num*a.den, a.den) does not fit in word
        FastRational a(INT_MIN,UINT_MAX);
        FastRational b(INT_MIN);
        FastRational sum = a+b;
        ASSERT_EQ(sum, FastRational("-9223372036854775808/4294967295"));
        ASSERT_FALSE(sum.wordPartValid());
    }
    {
        // b.den == 1
        // a.num + b.num*a.den does not fit in a word (but fits by definition in lword)
        FastRational a(INT_MAX,8);
        FastRational b(2);
        FastRational sum = a+b;
        ASSERT_EQ(sum, FastRational("2147483663/8"));
        ASSERT_FALSE(sum.wordPartValid());
    }
}

TEST_F(ArithmeticExpressions_test, test_subtraction)
{
    {
        FastRational a(10);
        FastRational b(0);
        FastRational c = a-b;
        ASSERT_EQ(c, a);
        ASSERT_TRUE(c.wordPartValid());
        ASSERT_FALSE(c.mpqPartValid());
    }
    {
        FastRational a(0);
        FastRational s = a - FastRational(INT_MIN);
        ASSERT_FALSE(s.wordPartValid());
        ASSERT_TRUE(s.mpqPartValid());
        ASSERT_EQ(s, FastRational(INT_MAX)+1);
    }
    {
        FastRational a(INT_MAX,UINT_MAX);
        FastRational b(INT_MIN);
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_TRUE(b.wordPartValid());
        ASSERT_FALSE(b.mpqMemoryAllocated());
        FastRational c = a - b;
        FastRational res("9223372036854775807/4294967295");
        ASSERT_TRUE(res.mpqPartValid());
        ASSERT_EQ(c, res);
    }
    {
        FastRational a(INT_MIN, UINT_MAX);
        FastRational b(INT_MAX);
        FastRational c = a - b;

    }
}

TEST_F(ArithmeticExpressions_test, test_division)
{
    {
        FastRational a(-1);
        FastRational b(-1);
        a /= b;
        ASSERT_EQ(a, 1);
    }
    {
        FastRational a(-3);
        FastRational b(2);
        a /= b;
        ASSERT_EQ(a, FastRational(-3, 2));
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
    }
}

TEST_F(ArithmeticExpressions_test, test_operatorAssign)
{
    {
        FastRational f(0);
        f -= FastRational(-3) * FastRational(-1);
        ASSERT_EQ(f, -3);
        ASSERT_TRUE(f.wordPartValid());
        ASSERT_FALSE(f.mpqMemoryAllocated());
    }
    {
        FastRational f(0);
        f += FastRational(-3) * FastRational(-1);
        ASSERT_EQ(f, 3);
        ASSERT_TRUE(f.wordPartValid());
        ASSERT_FALSE(f.mpqMemoryAllocated());
    }
    {
        // (/ 1333332 329664997) += (- 332667998001/329664997000)
        FastRational f(1333332, 329664997);
        f += -FastRational("332667998001/329664997000");
        // 331334666001/329664997000
        ASSERT_EQ(f, -FastRational("331334666001/329664997000"));
        ASSERT_TRUE(f.mpqMemoryAllocated());
        ASSERT_FALSE(f.wordPartValid());
    }
    {
        FastRational f(-1);
        f += FastRational("-1/2") * FastRational(-1);
        ASSERT_EQ(f, FastRational("-1/2"));
        ASSERT_TRUE(f.wordPartValid());
        ASSERT_FALSE(f.mpqMemoryAllocated());
    }
    {
        FastRational res = FastRational(1) - FastRational(0);
        ASSERT_EQ(res, 1);
        ASSERT_TRUE(res.wordPartValid());
        ASSERT_FALSE(res.mpqMemoryAllocated());
        // 1 - (/ (- 335) 666) = (/ (- 1001) 666)
        res = FastRational(1) - FastRational("-335/666");
        ASSERT_EQ(res, FastRational("1001/666"));
        ASSERT_TRUE(res.wordPartValid());
        ASSERT_FALSE(res.mpqMemoryAllocated());
    }
    {
        FastRational a(-1,12);
        FastRational b(-1);
        a += b;
        ASSERT_EQ(a, FastRational(-13,12));
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_TRUE(b.wordPartValid());
        ASSERT_FALSE(b.mpqMemoryAllocated());
    }
}

TEST_F(ArithmeticExpressions_test, test_CHECK_WORD)
{
    word a(INT_MAX);
    uword b(UINT_MAX);
    uword res;
    CHECK_WORD(res, lword(a)*b);
    ASSERT_EQ(res, (lword)(9223372030412324865));
    overflow:
    cout << "Overflow" << endl;
}