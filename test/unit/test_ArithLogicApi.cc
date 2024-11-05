//
// Created by Antti on 16.09.21.
//

#include <gtest/gtest.h>
#include <logics/ArithLogic.h>

namespace opensmt {

class ArithLogicApiTest: public ::testing::Test {
public:
    ArithLogicApiTest()
        : lraLogic(Logic_t::QF_LRA)
        , liaLogic(Logic_t::QF_LIA)
        , liraLogic(Logic_t::QF_LIRA)
    {}
    ArithLogic lraLogic;
    ArithLogic liaLogic;
    ArithLogic liraLogic;
};

TEST_F(ArithLogicApiTest, test_LRA) {
    PTRef c1 = lraLogic.mkConst("213");
    PTRef r1 = lraLogic.mkConst("213.0");
    ASSERT_EQ(c1, r1);
    ASSERT_TRUE(lraLogic.yieldsSortReal(c1));
    ASSERT_TRUE(lraLogic.yieldsSortReal(r1));
    PTRef c2 = lraLogic.mkRealVar("a");
    ASSERT_NO_THROW(lraLogic.mkPlus(c1, c2));
    ASSERT_NO_THROW(lraLogic.mkTimes(c2, c2));
    ASSERT_THROW(lraLogic.mkIntVar("x"), ApiException);
    ASSERT_THROW(lraLogic.mkIntConst(2), ApiException);
}

TEST_F(ArithLogicApiTest, test_LIA) {
    PTRef c1 = liaLogic.mkConst("213");
    ASSERT_TRUE(liaLogic.yieldsSortInt(c1));
    ASSERT_THROW(liaLogic.mkConst("213.0"), ApiException);
    PTRef c2 = liaLogic.mkIntVar("a");
    ASSERT_NO_THROW(liaLogic.mkPlus(c1, c2));
    ASSERT_NO_THROW(liaLogic.mkTimes(c2, c2));
    ASSERT_THROW(liaLogic.mkRealVar("a"), ApiException);
    ASSERT_THROW(liaLogic.mkRealConst(2), ApiException);
}

TEST_F(ArithLogicApiTest, test_Mixed) {
    PTRef c1 = liraLogic.mkConst("213");
    ASSERT_TRUE(liraLogic.yieldsSortInt(c1));
    PTRef r1 = liraLogic.mkConst("213.0");
    ASSERT_TRUE(liraLogic.yieldsSortReal(r1));
    PTRef c2 = liraLogic.mkRealVar("a");

    ASSERT_THROW(liraLogic.mkPlus(c1, c2), ApiException);
    ASSERT_THROW(liraLogic.mkEq(c1, c2), ApiException);
    PTRef d2 = liraLogic.mkIntVar("a");
    ASSERT_NO_THROW(liraLogic.mkPlus(c1, d2));
}

}
