//
// Created by Antti on 16.09.21.
//

#include <gtest/gtest.h>
#include <ArithLogic.h>

class ArithLogicApiTest: public ::testing::Test {
public:
    ArithLogicApiTest()
        : lraLogic(ArithLogic::ArithType::LRA)
        , liaLogic(ArithLogic::ArithType::LIA)
    {}
    ArithLogic lraLogic;
    ArithLogic liaLogic;
};

TEST_F(ArithLogicApiTest, test_LRA) {
    PTRef c1 = lraLogic.mkConst("213");
    PTRef c2 = lraLogic.mkNumVar("a");
    PTRef t1 = lraLogic.mkNumPlus(vec<PTRef>{c1, c2});
    PTRef t2 = lraLogic.mkRealPlus(vec<PTRef>{c1, c2});
    ASSERT_EQ(t1, t2);
    ASSERT_THROW(lraLogic.mkRealTimes(vec<PTRef>{c2, c2}), LANonLinearException);
    ASSERT_THROW(lraLogic.mkIntPlus(vec<PTRef>{c1, c2}), OsmtApiException);
}
