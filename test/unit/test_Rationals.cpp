#include <gtest/gtest.h>
#include <Real.h>

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
