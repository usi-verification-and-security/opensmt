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
    PTRef t1 = lraLogic.mkNumPlus({c1, c2});
    PTRef t2 = lraLogic.mkRealPlus({c1, c2});
    ASSERT_EQ(t1, t2);
    ASSERT_THROW(lraLogic.mkRealTimes({c2, c2}), LANonLinearException);
    ASSERT_THROW(lraLogic.mkIntPlus({c1, c2}), OsmtApiException);
}
