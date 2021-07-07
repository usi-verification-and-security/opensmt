//
// Created by Martin Blicha on 07.07.21.
//

#include <gtest/gtest.h>
#include <PG.h>

TEST(ProofTest, test_mergeClauses_PivotPresent_NoDuplicates) {
    std::vector<Lit> left { mkLit(0, true), mkLit(1,false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 2);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
}

TEST(ProofTest, test_mergeClauses_PivotPresent_Duplicates) {
    std::vector<Lit> left { mkLit(0, true), mkLit(1,false), mkLit(2,false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false), mkLit(3,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 3);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
    EXPECT_EQ(res[2], mkLit(3,false));
}

TEST(ProofTest, test_mergeClauses_GarbageInResult) {
    std::vector<Lit> left { mkLit(0, true), mkLit(1,false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false) };
    std::vector<Lit> res { mkLit(100, true), mkLit(42, false), mkLit(0, true), mkLit(0, true) };
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 2);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
}

TEST(ProofTest, test_mergeClauses_DuplicateAfterFirstEnd) {
    std::vector<Lit> left { mkLit(0, true), mkLit(1,false), mkLit(4,false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false), mkLit(3,false), mkLit(4,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 4);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
    EXPECT_EQ(res[2], mkLit(3,false));
    EXPECT_EQ(res[3], mkLit(4,false));
}

TEST(ProofTest, test_mergeClauses_DuplicateAfterSecondEnd) {
    std::vector<Lit> left { mkLit(1, true), mkLit(2,false), mkLit(3,false), mkLit(4,false) };
    std::vector<Lit> right { mkLit(0, true), mkLit(1,false), mkLit(4,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 4);
    EXPECT_EQ(res[0], mkLit(0,true));
    EXPECT_EQ(res[1], mkLit(2,false));
    EXPECT_EQ(res[2], mkLit(3,false));
    EXPECT_EQ(res[3], mkLit(4,false));
}

TEST(ProofTest, test_mergeClauses_PivotAfterSecondEnd) {
    std::vector<Lit> left { mkLit(1, true), mkLit(2,false), mkLit(3,false), mkLit(4,false) };
    std::vector<Lit> right { mkLit(1, false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 3);
    EXPECT_EQ(res[0], mkLit(2,false));
    EXPECT_EQ(res[1], mkLit(3,false));
    EXPECT_EQ(res[2], mkLit(4,false));
}

TEST(ProofTest, test_mergeClauses_PivotAfterFirstEnd) {
    std::vector<Lit> left { mkLit(1, false) };
    std::vector<Lit> right { mkLit(1, true), mkLit(2,false), mkLit(3,false), mkLit(4,false) };
    std::vector<Lit> res;
    Var pivot = 1;
    ProofGraph::mergeClauses(left, right, res, pivot);
    ASSERT_EQ(res.size(), 3);
    EXPECT_EQ(res[0], mkLit(2,false));
    EXPECT_EQ(res[1], mkLit(3,false));
    EXPECT_EQ(res[2], mkLit(4,false));
}
