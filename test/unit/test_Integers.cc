#include <gtest/gtest.h>
#include <common/Integer.h>
#include <common/Real.h>

namespace opensmt {

TEST(Integers_test, test_negate_int32min) {
    // INT32_MIN
    Integer i {"-2147483648"};
    i.negate();
    EXPECT_TRUE(i > 0);
}

TEST(Integers_test, test_negate_minus_int32min) {
    // - INT32_MIN = 2^31
    Integer i {"2147483648"};
    Integer neg = -i;
    EXPECT_TRUE(neg.isWellFormed());
    EXPECT_TRUE(neg < 0);
    i.negate();
    EXPECT_TRUE(i.isWellFormed());
    EXPECT_EQ(i, neg);
}

TEST(Integers_test, test_additionAssign) {
    Integer a {"2147483640"};
    Integer b {"10"};
    additionAssign(a,b);
    EXPECT_EQ(a, Integer{"2147483650"} );
}

TEST(Integers_test, test_overwrite)
{
    Integer i(INT32_MAX);
    Integer q(0);
    i *= 10;
    // should not compile:
    // i *= Real(5, 4);
    i = 0;
    i = INT32_MAX;
    i *= 10;
    i = q;
}

TEST(Integers_test, test_uword)
{
    uint32_t x = 2589903246;
    Integer f(x);
    ASSERT_TRUE(f.mpqPartValid());
}

TEST(Integers_test, test_modulo)
{
    Integer a(-37033300);
    Integer b(1);
    Integer mod = a % b;
    ASSERT_EQ(mod, 0);
}

TEST(Integers_test, test_creation)
{
    {
        Integer a{INT_MIN};
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_EQ(a, Integer{"-2147483648"});
    }
    {
        Integer a{INT_MAX};
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_EQ(a, Integer{"2147483647"});
    }
}

TEST(Integers_test, test_addition)
{
    {
        Integer a(3);
        Integer b(0);
        static_assert(std::is_same_v<decltype(a + b), Integer>);
        ASSERT_EQ(a + b, Integer(3));
        ASSERT_EQ(-a + b, Integer(-3));
    }

    {
        Integer a(0);
        Integer b(3);
        ASSERT_EQ(a + b, Integer(3));
        ASSERT_EQ(a + (-b), Integer(-3));
    }

    {
        Integer a(3);
        Integer b(-3);
        ASSERT_EQ(a+b, 0);
    }

    {
        Integer a(3);
        Integer b(1);
        ASSERT_EQ(a+b, Integer(4));
    }
    {
        Integer a(UINT_MAX);
        Integer b(INT_MAX);
        Integer sum = a+b;
        ASSERT_EQ(sum, Integer("6442450942"));
        ASSERT_FALSE(sum.wordPartValid());
    }
    {
        Integer a(UINT_MAX);
        Integer b(INT_MIN);
        Integer sum = a+b;
        ASSERT_EQ(sum, Integer("2147483647"));
        ASSERT_TRUE(sum.wordPartValid());
    }
}

TEST(Integers_test, test_subtraction)
{
    {
        Integer a(10);
        Integer b(0);
        static_assert(std::is_same_v<decltype(a - b), Integer>);
        Integer c = a-b;
        ASSERT_EQ(c, a);
        ASSERT_TRUE(c.wordPartValid());
        ASSERT_FALSE(c.mpqPartValid());
    }
    {
        Integer a(0);
        Integer s = a - Integer(INT_MIN);
        ASSERT_FALSE(s.wordPartValid());
        ASSERT_TRUE(s.mpqPartValid());
        ASSERT_EQ(s, Integer(INT_MAX)+1);
    }
    {
        Integer a(INT_MAX);
        Integer b(UINT_MAX);
        Integer sum = a-b;
        ASSERT_EQ(sum, Integer("-2147483648"));
        ASSERT_TRUE(sum.wordPartValid());
    }
}

TEST(Integers_test, test_division)
{
    {
        Integer a(-1);
        Integer b(-1);
        Real c = a / b;
        ASSERT_EQ(c, 1);
    }
    {
        Integer a(-3);
        Integer b(2);
        Real c = a / b;
        ASSERT_EQ(c, Real(-3, 2));
        ASSERT_TRUE(c.wordPartValid());
        ASSERT_FALSE(c.mpqMemoryAllocated());
    }
}

TEST(Integers_test, test_operatorAssign)
{
    {
        Integer f(0);
        static_assert(std::is_same_v<decltype(Integer(-3) * Integer(-1)), Integer>);
        f -= Integer(-3) * Integer(-1);
        ASSERT_EQ(f, -3);
        ASSERT_TRUE(f.wordPartValid());
        ASSERT_FALSE(f.mpqMemoryAllocated());
    }
    {
        Integer f(0);
        f += Integer(-3) * Integer(-1);
        ASSERT_EQ(f, 3);
        ASSERT_TRUE(f.wordPartValid());
        ASSERT_FALSE(f.mpqMemoryAllocated());
    }
}

TEST(Integers_test, test_CHECK_WORD)
{
    word a(INT_MAX);
    uword b(UINT_MAX);
    uword res = 0;
    CHECK_WORD(res, lword(a)*b);
    ASSERT_EQ(res, (lword)(9223372030412324865));
    overflow:
    std::cout << "Overflow" << std::endl;
}

TEST(Integers_test, test_sub_lword_underflow_min)
{
    lword res;
    (void)res;
    lword s1 = 0;
    lword s2 = LWORD_MIN;
    CHECK_SUB_OVERFLOWS_LWORD(res, s1, s2);
    ASSERT_TRUE(false);
    overflow:
    ASSERT_TRUE(true);
}

TEST(Integers_test, test_sub_lword_nounderflow)
{
    lword res;
    (void)res;
    lword s1 = 0;
    lword s2 = LWORD_MIN+1;
    CHECK_SUB_OVERFLOWS_LWORD(res, s1, s2);
    return;
    overflow:
    ASSERT_TRUE(false);
}

TEST(Integers_test, test_sub_lword_nooverflow)
{
    lword res;
    (void)res;
    lword s1 = -1;
    lword s2 = LWORD_MAX;
    CHECK_SUB_OVERFLOWS_LWORD(res, s1, s2);
    return;
    overflow:
    ASSERT_TRUE(false);
}

TEST(Integers_test, test_sub_lword_overflow)
{
    lword res;
    (void)res;
    lword s1 = -2;
    lword s2 = LWORD_MAX;
    CHECK_SUB_OVERFLOWS_LWORD(res, s1, s2);
    ASSERT_FALSE(true);
    overflow:
    ASSERT_TRUE(true);
}

TEST(Integers_test, test_mod)
{
    Integer a(INT_MAX);
    Integer b(INT_MIN);
    Integer res = a % b;
    ASSERT_EQ(res, (INT_MIN+1));
}

TEST(Integers_test, test_addNegated)
{
    {
        Integer a(15);
        Integer b(-15);
        Integer res = a+b;
        ASSERT_EQ(res, 0);
    }
    {
        Integer a(INT_MAX);
        Integer b(INT_MIN);
        Integer res = a + b;
        ASSERT_EQ(res, -1);
    }
}

TEST(Integers_test, testWordRepresentation_Negate) {
    Integer a(INT_MIN); // a fits into word representation
    ASSERT_TRUE(a.wordPartValid());
    a.negate(); // a now does not fit into word representation
    ASSERT_FALSE(a.wordPartValid());
    a.negate(); // a now again fits into word representation
    ASSERT_TRUE(a.wordPartValid());
}

}
