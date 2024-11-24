#include <gtest/gtest.h>
#include <common/numbers/Real.h>

#include <vector>

namespace opensmt {

TEST(Rationals_test, test_division_int32min)
{
    // INT32_MIN
    Real r {"-2147483648"};
    ASSERT_LT(r,0);
    Real nom = r/2047;
    Real den = r/3071;
    ASSERT_LT(nom, 0);
    ASSERT_LT(den, 0);
    ASSERT_GT(nom/den, 0);
    nom /= den;
    ASSERT_GT(nom, 0);
}

TEST(Rationals_test, test_abs_val_int32min)
{
    int32_t x = -2147483648;
    ASSERT_EQ(absVal(x), 2147483648);
}

TEST(Rationals_test, test_normalized)
{
    Real toNormalize(2,4);
    EXPECT_EQ(toNormalize.get_num(), 1);
    EXPECT_EQ(toNormalize.get_den(), 2);
}

TEST(Rationals_test, test_hash_function)
{
    std::vector<uint32_t> hashes;
    Real::Hash hasher;
    for (int i = 0; i < 10; i++) {
        Real r((int)random());
        hashes.push_back(hasher(r));
    }
    for (int i = 0; i < 10; i++) {
        Real r(i);
        hashes.push_back(hasher(r));
    }
    for (int i = 0; i < 10; i++) {
        char* str;
        int written = asprintf(&str, "%ld/%u", random(), UINT32_MAX);
        assert(written != -1); (void)written;
        Real r(str);
        free(str);
        hashes.push_back(hasher(r));
    }

    for (int i = 0; i < 10; i++) {
        char num_str[21];
        for (int j = 0; j < 20; j++) {
            num_str[j] = 48+(random() % 10);
        }
        num_str[20] = 0;
        char den_str[21];
        for (int j = 0; j < 20; j++) {
            den_str[j] = 48+(random() % 10);
        }
        den_str[20] = 0;
        char *str;
        int written = asprintf(&str, "%s/%s", num_str, den_str);
        assert(written != -1); (void)written;
        Real r(str);
        free(str);
        hashes.push_back(hasher(r));
    }

    for (int k = 0; k < 10; k++) {
        char den_str[21];
        for (int j = 0; j < 19; j++) {
            den_str[j] = 48+(random() % 10);
        }
        den_str[20] = 0;

        for (int i = 0; i < 10; i++) {
            den_str[19] = 48 + i;
            char *str;
            int written = asprintf(&str, "1/%s", den_str);
            assert(written != -1); (void)written;
            Real r(str);
            free(str);
            hashes.push_back(hasher(r));
        }
    }
    std::sort(hashes.begin(), hashes.end());
    int prev = hashes[0];
    for (std::size_t i = 1; i < hashes.size(); i++) {
        ASSERT_NE(prev, hashes[i]);
        prev = hashes[i];
    }
}

TEST(Rationals_test, test_doubleRepresentation) {
    int val = 100000;
    Real r{val};
    Real overflow = r * r;
    EXPECT_TRUE(overflow > 0);
    r.negate();
    Real res = r * val;
    EXPECT_TRUE(res < 0);
}

TEST(Rationals_test, test_negate_int32min) {
    // INT32_MIN
    Real r {"-2147483648"};
    r.negate();
    EXPECT_TRUE(r > 0);
}

TEST(Rationals_test, test_negate_minus_int32min) {
    // - INT32_MIN = 2^31
    Real r {"2147483648"};
    Real neg = -r;
    EXPECT_TRUE(neg.isWellFormed());
    EXPECT_TRUE(neg < 0);
    r.negate();
    EXPECT_TRUE(r.isWellFormed());
    EXPECT_EQ(r, neg);
}

TEST(Rationals_test, test_additionAssign) {
    Real a {"2147483640"};
    Real b {"10"};
    additionAssign(a,b);
    EXPECT_EQ(a, Real{"2147483650"} );
}

TEST(Rationals_test, test_overwrite)
{
    Real r(INT32_MAX);
    Real q(0);
    r *= 10;
    r = 0;
    r = INT32_MAX;
    r *= 10;
    r = q;
}

TEST(Rationals_test, test_uword)
{
    uint32_t x = 2589903246;
    Real f(x);
    ASSERT_TRUE(f.mpqPartValid());
}

TEST(Rationals_test, test_creation)
{
    {
        // a = INT_MIN / INT_MAX is the number that has the smallest nominator and biggest denominator such that it still fits the word representation
        Real a(INT_MIN, INT_MAX);
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_EQ(a, Real("-2147483648/2147483647"));
    }
    {
        // a = INT_MAX / INT_MAX = 1 but in current implementation handles big values.
        Real a(INT_MAX,INT_MAX);
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_EQ(a, 1);
    }
}

TEST(Rationals_test, test_addition)
{
    {
        // b.num == 0
        Real a(1, 3);
        Real b(0);
        ASSERT_EQ(a + b, Real(1, 3));
        ASSERT_EQ(-a + b, Real(-1, 3));
    }

    {
        // a.num == 0
        Real a(0);
        Real b(1, 3);
        ASSERT_EQ(a + b, Real(1, 3));
        ASSERT_EQ(a + (-b), Real(-1, 3));
    }

    {
        // a == -b
        Real a(1,3);
        Real b(-1,3);
        ASSERT_EQ(a+b, 0);
    }

    {
        // b.den == 1
        // result fits in word
        Real a(1,3);
        Real b(1);
        ASSERT_EQ(a+b, Real(4,3));
    }
    {
        // b.den == 1
        // a.num + b.num*a.den does not fit in word (but fits by definition in lword)
        // (a.num + b.num*a.den) / gcd(a.num+b.num*a.den, a.den) does not fit in word
        Real a(INT_MAX,UINT_MAX);
        Real b(INT_MAX);
        Real sum = a+b;
        ASSERT_EQ(sum, Real("9223372032559808512/4294967295"));
        ASSERT_FALSE(sum.wordPartValid());
    }
    {
        // b.den == 1
        // a and b negative
        // a.num + b.num*a.den does not fit in word (but fits by definition in lword)
        // (a.num + b.num*a.den) / gcd(a.num+b.num*a.den, a.den) does not fit in word
        Real a(INT_MIN,UINT_MAX);
        Real b(INT_MIN);
        Real sum = a+b;
        ASSERT_EQ(sum, Real("-9223372036854775808/4294967295"));
        ASSERT_FALSE(sum.wordPartValid());
    }
    {
        // b.den == 1
        // a.num + b.num*a.den does not fit in a word (but fits by definition in lword)
        Real a(INT_MAX,8);
        Real b(2);
        Real sum = a+b;
        ASSERT_EQ(sum, Real("2147483663/8"));
        ASSERT_FALSE(sum.wordPartValid());
    }
}

TEST(Rationals_test, test_multiplicand)
{
    {
        std::vector<Real> rs{Real(1, 3), Real(1, 5), Real(1, 6)};
        Real mul = get_multiplicand(rs);
        ASSERT_EQ(mul, 30);
    }
    {
        std::vector<Real> rs{Real(1, 3), Real(1, 5), Real(2, 5)};
        Real mul = get_multiplicand(rs);
        ASSERT_EQ(mul, 15);
    }
}

TEST(Rationals_test, test_subtraction)
{
    {
        Real a(10);
        Real b(0);
        Real c = a-b;
        ASSERT_EQ(c, a);
        ASSERT_TRUE(c.wordPartValid());
        ASSERT_FALSE(c.mpqPartValid());
    }
    {
        Real a(0);
        Real s = a - Real(INT_MIN);
        ASSERT_FALSE(s.wordPartValid());
        ASSERT_TRUE(s.mpqPartValid());
        ASSERT_EQ(s, Real(INT_MAX)+1);
    }
    {
        Real a(INT_MAX,UINT_MAX);
        Real b(INT_MIN);
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_TRUE(b.wordPartValid());
        ASSERT_FALSE(b.mpqMemoryAllocated());
        Real c = a - b;
        Real res("9223372036854775807/4294967295");
        ASSERT_TRUE(res.mpqPartValid());
        ASSERT_EQ(c, res);
    }
    {
        Real a(INT_MIN, UINT_MAX);
        Real b(INT_MAX);
        Real c = a - b;

    }
    {
        Real a("-2147483645/4294967294");
        Real b("2147483647/4294967295");
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_TRUE(b.wordPartValid());
        Real c = a - b;
        ASSERT_TRUE(c.mpqPartValid());
        Real res("-18446744050087231493/18446744060824649730");
        ASSERT_EQ(c, res);
    }
    {
        Real a("-2147483647/4294967292");
        Real b("2147483645/4294967294");
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_TRUE(b.wordPartValid());
        Real c = a - b;
        ASSERT_TRUE(c.mpqPartValid());
    }
}

TEST(Rationals_test, test_division)
{
    {
        Real a(-1);
        Real b(-1);
        a /= b;
        ASSERT_EQ(a, 1);
    }
    {
        Real a(-3);
        Real b(2);
        a /= b;
        ASSERT_EQ(a, Real(-3, 2));
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
    }
}

TEST(Rationals_test, test_operatorAssign)
{
    {
        Real f(0);
        f -= Real(-3) * Real(-1);
        ASSERT_EQ(f, -3);
        ASSERT_TRUE(f.wordPartValid());
        ASSERT_FALSE(f.mpqMemoryAllocated());
    }
    {
        Real f(0);
        f += Real(-3) * Real(-1);
        ASSERT_EQ(f, 3);
        ASSERT_TRUE(f.wordPartValid());
        ASSERT_FALSE(f.mpqMemoryAllocated());
    }
    {
        // (/ 1333332 329664997) += (- 332667998001/329664997000)
        Real f(1333332, 329664997);
        f += -Real("332667998001/329664997000");
        // 331334666001/329664997000
        ASSERT_EQ(f, -Real("331334666001/329664997000"));
        ASSERT_TRUE(f.mpqMemoryAllocated());
        ASSERT_FALSE(f.wordPartValid());
    }
    {
        Real f(-1);
        f += Real("-1/2") * Real(-1);
        ASSERT_EQ(f, Real("-1/2"));
        ASSERT_TRUE(f.wordPartValid());
        ASSERT_FALSE(f.mpqMemoryAllocated());
    }
    {
        Real res = Real(1) - Real(0);
        ASSERT_EQ(res, 1);
        ASSERT_TRUE(res.wordPartValid());
        ASSERT_FALSE(res.mpqMemoryAllocated());
        // 1 - (/ (- 335) 666) = (/ (- 1001) 666)
        res = Real(1) - Real("-335/666");
        ASSERT_EQ(res, Real("1001/666"));
        ASSERT_TRUE(res.wordPartValid());
        ASSERT_FALSE(res.mpqMemoryAllocated());
    }
    {
        Real a(-1,12);
        Real b(-1);
        a += b;
        ASSERT_EQ(a, Real(-13,12));
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_FALSE(a.mpqMemoryAllocated());
        ASSERT_TRUE(b.wordPartValid());
        ASSERT_FALSE(b.mpqMemoryAllocated());
    }
}

TEST(Rationals_test, test_CHECK_WORD)
{
    word a(INT_MAX);
    uword b(UINT_MAX);
    uword res = 0;
    CHECK_WORD(res, lword(a)*b);
    ASSERT_EQ(res, (lword)(9223372030412324865));
    overflow:
    std::cout << "Overflow" << std::endl;
}

TEST(Rationals_test, test_sub_lword_underflow_min)
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

TEST(Rationals_test, test_sub_lword_nounderflow)
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

TEST(Rationals_test, test_sub_lword_nooverflow)
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

TEST(Rationals_test, test_sub_lword_overflow)
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

TEST(Rationals_test, test_ceil)
{
    word a(INT_MIN);
    uword b(3);
    Real f(a, b);
    f.ceil();
}

TEST(Rationals_test, test_addNegated)
{
    {
        Real a(15);
        Real b(-15);
        Real res = a+b;
        ASSERT_EQ(res, 0);
    }
    {
        Real a(INT_MAX);
        Real b(INT_MIN);
        Real res = a + b;
        ASSERT_EQ(res, -1);
    }
}

TEST(Rationals_test, testWordRepresentation_Negate) {
    Real a(INT_MIN); // a fits into word representation
    ASSERT_TRUE(a.wordPartValid());
    a.negate(); // a now does not fit into word representation
    ASSERT_FALSE(a.wordPartValid());
    a.negate(); // a now again fits into word representation
    ASSERT_TRUE(a.wordPartValid());
}

TEST(Rationals_test, testWordRepresentation_Inverse) {
    uword val = INT_MAX;
    ++val;
    Real a(1, val); // a fits into word representation
    ASSERT_TRUE(a.wordPartValid());
    a = a.inverse(); // a now does not fit into word representation
    ASSERT_FALSE(a.wordPartValid());
    a = a.inverse(); // a now again fits into word representation
    ASSERT_TRUE(a.wordPartValid());
}

TEST(Rationals_test, testNormalization) {
    word num = -3703870;
    uword den = 10000000;
    // GCD of num and den is 10
    Real a(num, den);
    auto maybeNumDenPair = a.tryGetNumDen();
    ASSERT_TRUE(maybeNumDenPair.has_value());
    auto [normalizedNum, normalizedDen] = maybeNumDenPair.value();
    EXPECT_EQ(normalizedNum, -370387);
    EXPECT_EQ(normalizedDen, 1000000);
}

}
