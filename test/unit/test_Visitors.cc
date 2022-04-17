/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include <gtest/gtest.h>
#include <ArithLogic.h>
#include <TreeOps.h>

#include <algorithm>

class VisitorTest : public ::testing::Test {
protected:
    VisitorTest() : logic{opensmt::Logic_t::QF_LRA} {}

    virtual void SetUp() {
        x = logic.mkRealVar("x");
        y = logic.mkRealVar("y");
        z = logic.mkRealVar("z");
        b = logic.mkBoolVar("b");
    }

    ArithLogic logic;
    PTRef x, y, z;
    PTRef b;

    bool contains(vec<PTRef> const & terms, PTRef term) const { return std::find(terms.begin(), terms.end(), term) != terms.end(); }
};

TEST_F(VisitorTest, test_GetVariablesZero) {
    auto vars = variables(logic, logic.getTerm_RealZero());
    ASSERT_TRUE(vars.size() == 0);
}

TEST_F(VisitorTest, test_GetVariablesOne) {
    auto vars = variables(logic, x);
    ASSERT_TRUE(vars.size() == 1);
    ASSERT_EQ(vars[0], x);
}

TEST_F(VisitorTest, test_GetVariablesMany) {
    auto vars = variables(logic, logic.mkPlus(vec<PTRef>{x, y, logic.mkTimes(z, logic.mkRealConst(2))}));
    ASSERT_TRUE(vars.size() == 3);
    EXPECT_TRUE(contains(vars,x));
    EXPECT_TRUE(contains(vars,y));
    EXPECT_TRUE(contains(vars,z));
}

TEST_F(VisitorTest, test_GetVariablesNoDuplicates) {
    PTRef term = logic.mkAnd(logic.mkGeq(x, y), logic.mkGeq(x,z));
    auto vars = variables(logic, term);
    ASSERT_TRUE(vars.size() == 3);
    EXPECT_TRUE(contains(vars,x));
    EXPECT_TRUE(contains(vars,y));
    EXPECT_TRUE(contains(vars,z));
}

TEST_F(VisitorTest, test_GetAllSubTermsConstant) {
    auto subterms = subTerms(logic, logic.getTerm_true());
    ASSERT_TRUE(subterms.size() == 1);
    ASSERT_EQ(subterms[0], logic.getTerm_true());
}

TEST_F(VisitorTest, test_GetAllSubTermsBasicSum) {
    PTRef sum = logic.mkPlus(x,y);
    auto subterms = subTerms(logic, sum);
    ASSERT_TRUE(subterms.size() == 3);
    EXPECT_TRUE(contains(subterms,x));
    EXPECT_TRUE(contains(subterms,y));
    EXPECT_TRUE(contains(subterms,sum));
}

TEST_F(VisitorTest, test_GetSubTermsArbitraryPredicate) {
    PTRef zero = logic.getTerm_RealZero();
    PTRef plus1 = logic.mkPlus(x,y);
    PTRef plus2 = logic.mkPlus(x,z);
    PTRef fla = logic.mkAnd(logic.mkGeq(plus1, zero), logic.mkGeq(plus2, zero));
    auto subterms = subTerms(logic, fla, [&](PTRef subterm) { return logic.isPlus(subterm); });
    ASSERT_TRUE(subterms.size() == 2);
    EXPECT_TRUE(contains(subterms,plus1));
    EXPECT_TRUE(contains(subterms,plus2));
}
