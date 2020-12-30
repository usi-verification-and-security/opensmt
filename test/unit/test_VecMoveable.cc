#include <gtest/gtest.h>
#include <Pterm.h>
#include <type_traits>

class VecTest: public ::testing::Test {
public:
    class Foo {
        vec<PTLKey> v;
    };
    VecTest() {}
};

TEST_F(VecTest, test_VecMoveable) {
    ASSERT_FALSE(std::is_trivially_copyable<Foo>());
}

