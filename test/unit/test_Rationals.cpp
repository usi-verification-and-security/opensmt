#include <gtest/gtest.h>
#include <Real.h>
#include <stdlib.h>
#include <Vec.h>
#include <Sort.h>

using Real = opensmt::Real;

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
    FastRational toNormalize(2,4);
    EXPECT_EQ(toNormalize.get_num(), 1);
    EXPECT_EQ(toNormalize.get_den(), 2);
}

TEST(Rationals_test, test_hash_function)
{
    vec<uint32_t> hashes;
    for (int i = 0; i < 10; i++) {
        Real r((int)random());
        hashes.push(r.getHashValue());
    }
    for (int i = 0; i < 10; i++) {
        Real r(i);
        hashes.push(r.getHashValue());
    }
    for (int i = 0; i < 10; i++) {
        char* str;
        int written = asprintf(&str, "%ld/%u", random(), UINT32_MAX);
        assert(written != -1); (void)written;
        Real r(str);
        free(str);
        hashes.push(r.getHashValue());
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
        hashes.push(r.getHashValue());
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
            hashes.push(r.getHashValue());
        }
    }
    sort(hashes);
    int prev = hashes[0];
    for (int i = 1; i < hashes.size(); i++) {
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

TEST(Rationals_test, test_unique)
{
    vec<Real> v = {1, 1, 2, 3, 3, 4};
    vec<Real> w = {1, 2, 3, 4};
    uniq(v);
    ASSERT_EQ(v.size(), w.size());
    for (int i = 0; i < v.size(); i++)
        ASSERT_EQ(v[i], w[i]);
}

TEST(Rationals_test, test_uword)
{
    uint32_t x = 2589903246;
    FastRational f(x);
    ASSERT_TRUE(f.mpqPartValid());
}

TEST(Rationals_test, test_modulo)
{
    FastRational a(-37033300);
    FastRational b(1);
    FastRational mod = a % b;
    ASSERT_EQ(mod, 0);
}

TEST(Rationals_test, test_creation)
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

TEST(Rationals_test, test_addition)
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

TEST(Rationals_test, test_subtraction)
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
    {
        FastRational a("-2147483645/4294967294");
        FastRational b("2147483647/4294967295");
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_TRUE(b.wordPartValid());
        FastRational c = a - b;
        ASSERT_TRUE(c.mpqPartValid());
        FastRational res("-18446744050087231493/18446744060824649730");
        ASSERT_EQ(c, res);
    }
    {
        FastRational a("-2147483647/4294967292");
        FastRational b("2147483645/4294967294");
        ASSERT_TRUE(a.wordPartValid());
        ASSERT_TRUE(b.wordPartValid());
        FastRational c = a - b;
        ASSERT_TRUE(c.mpqPartValid());
    }
}

TEST(Rationals_test, test_division)
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

TEST(Rationals_test, test_operatorAssign)
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

TEST(Rationals_test, test_CHECK_WORD)
{
    word a(INT_MAX);
    uword b(UINT_MAX);
    uword res;
    CHECK_WORD(res, lword(a)*b);
    ASSERT_EQ(res, (lword)(9223372030412324865));
    overflow:
    std::cout << "Overflow" << std::endl;
}

TEST(Rationals_test, test_sub_lword_underflow_min)
{
    lword res;
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
    FastRational f(a, b);
    f.ceil();
}

TEST(Rationals_test, test_mod)
{
    FastRational a(INT_MAX);
    FastRational b(INT_MIN);
    FastRational res = a % b;
    ASSERT_EQ(res, (INT_MIN+1));
}

TEST(Rationals_test, test_addNegated)
{
    {
        FastRational a(15);
        FastRational b(-15);
        FastRational res = a+b;
        ASSERT_EQ(res, 0);
    }
    {
        FastRational a(INT_MAX);
        FastRational b(INT_MIN);
        FastRational res = a + b;
        ASSERT_EQ(res, -1);
    }
}

