#include <gtest/gtest.h>
#include <tsolvers/lasolver/Delta.h>

namespace opensmt {

TEST(Delta_test, test_ops_in_Delta)
{
    Delta plus_infty(Delta::UPPER);
    Delta minus_infty(Delta::LOWER);
    ASSERT_EQ(plus_infty.isPlusInf(),         true);
    ASSERT_EQ(minus_infty.isMinusInf(),       true);
    ASSERT_EQ(minus_infty < plus_infty,   true);
    ASSERT_EQ(minus_infty <= plus_infty,  true);
    ASSERT_EQ(plus_infty > minus_infty,   true);
    ASSERT_EQ(plus_infty >= minus_infty,  true);
    ASSERT_EQ(!(plus_infty < minus_infty),  true);
    ASSERT_EQ(!(plus_infty < minus_infty), true);
    ASSERT_EQ(!(minus_infty > plus_infty),  true);
    ASSERT_EQ(!(minus_infty >= plus_infty), true);
}

}
