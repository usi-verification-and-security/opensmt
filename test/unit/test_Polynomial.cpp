/*
 *  Copyright (c) 2019-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include <lasolver/Polynomial.h>
#include <lasolver/LAVar.h>

using Polynomial = PolynomialT<LVRef>;

class PolyTest : public ::testing::Test {
protected:
    Polynomial::poly_t tmp_storage {};
    Polynomial poly1 {};
    Polynomial poly2 {};
};

TEST_F(PolyTest, test_AddTerm){
    LVRef var {10};
    poly1.addTerm(var, 1);
    EXPECT_EQ(poly1.getCoeff(var), 1);
}

TEST_F(PolyTest, test_Merge){
    LVRef x {10};
    LVRef y {20};
    LVRef z {30};
    poly1.addTerm(x, 1);
    poly1.addTerm(y, -3);
    poly2.addTerm(z, 1);
    poly2.addTerm(y, 3);
    std::vector<LVRef> added;
    std::vector<LVRef> removed;
    auto add = [&added](LVRef v) { added.push_back(v); };
    auto remove = [&removed](LVRef v) { removed.push_back(v); };
    poly1.merge(poly2, 1, tmp_storage, add, remove);
    ASSERT_EQ(added.size(),1);
    EXPECT_EQ(added[0], z);
    ASSERT_EQ(removed.size(),1);
    EXPECT_EQ(removed[0], y);
    ASSERT_TRUE(poly1.contains(x));
    ASSERT_TRUE(poly1.contains(z));
    EXPECT_FALSE(poly1.contains(y));
    EXPECT_EQ(poly1.getCoeff(x), 1);
    EXPECT_EQ(poly1.getCoeff(z), 1);
}

TEST_F(PolyTest, test_Merge2){
    LVRef x1 {4772};
    LVRef x2 {4776};
    LVRef y1 {2604};
    LVRef y2 {4624};
    poly1.addTerm(x1, 1);
    poly1.addTerm(x2, -1);
    poly2.addTerm(y1, -1);
    poly2.addTerm(y2, 1);
    std::vector<LVRef> added;
    std::vector<LVRef> removed;
    auto add = [&added](LVRef v) { added.push_back(v); };
    auto remove = [&removed](LVRef v) { removed.push_back(v); };
    poly1.merge(poly2, 1, tmp_storage, add, remove);
    ASSERT_EQ(added.size(),2);
    ASSERT_EQ(removed.size(),0);
    ASSERT_TRUE(poly1.contains(x1));
    ASSERT_TRUE(poly1.contains(x2));
    ASSERT_TRUE(poly1.contains(y1));
    ASSERT_TRUE(poly1.contains(y2));
}

TEST_F(PolyTest, test_Merge3){
    LVRef x1 {4772};
    LVRef x2 {4776};
    poly1.addTerm(x1, 1);
    poly1.addTerm(x2, -2);
    poly2.addTerm(x2, 1);
    std::vector<LVRef> added;
    std::vector<LVRef> removed;
    auto add = [&added](LVRef v) { added.push_back(v); };
    auto remove = [&removed](LVRef v) { removed.push_back(v); };
    poly1.merge(poly2, 2, tmp_storage, add, remove);
    ASSERT_EQ(added.size(),0);
    ASSERT_EQ(removed.size(),1);
    EXPECT_EQ(removed[0], x2);
    ASSERT_TRUE(poly1.contains(x1));
    ASSERT_TRUE(!poly1.contains(x2));
}