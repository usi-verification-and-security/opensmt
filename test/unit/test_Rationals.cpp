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
