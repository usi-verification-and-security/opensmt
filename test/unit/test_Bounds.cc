//
// Created by Antti on 31.03.20.
//
#include <gtest/gtest.h>
#include <LABounds.h>

class BoundTest: public ::testing::Test {
public:
    BoundTest() {}
};

TEST_F(BoundTest, test_LABounds) {
    LAVarStore vs;
    LABoundStore bs(vs);
    for (int k = 0; k < 100; k++) {
        vec<LVRef> vars;
        for (int i = 0; i < 100; i++) {
            vars.push(vs.getNewVar());
            for (int j = 0; j < 10; j++) {
                bs.allocBoundPair(vars[i], j, j % 2);
            }
        }
        bs.buildBounds();
        bs.clear();
    }
}
