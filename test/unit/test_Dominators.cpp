//
// Created by Martin Blicha on 31.10.18.
//

#include <gtest/gtest.h>
#include <BoolRewriting.h>
#include <Logic.h>
#include <algorithm>

TEST(Dominators_test, test_PostOrderSimpleTree)
{
    Logic logic;
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef conj = logic.mkAnd(a,b);
    auto postOrder = getPostOrder(conj, logic);
    ASSERT_EQ(postOrder.size(), 3);
    ASSERT_EQ(postOrder[2], conj);
}

TEST(Dominators_test, test_PostOrderSimpleDAG)
{
    Logic logic;
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef conj = logic.mkAnd(a,b);
    PTRef neg = logic.mkNot(a);
    PTRef root = logic.mkOr(neg, conj);
    auto postOrder = getPostOrder(root, logic);
    ASSERT_EQ(postOrder.size(), 5);
    ASSERT_EQ(postOrder[4], root);
    ASSERT_GT(std::find(postOrder.begin(), postOrder.end(), neg) - std::find(postOrder.begin(), postOrder.end(), a), 0);
    ASSERT_GT(std::find(postOrder.begin(), postOrder.end(), conj) - std::find(postOrder.begin(), postOrder.end(), a), 0);
    ASSERT_GT(std::find(postOrder.begin(), postOrder.end(), conj) - std::find(postOrder.begin(), postOrder.end(), b), 0);
}


TEST(Dominators_test, test_Trivial)
{
    Logic logic;
    PTRef a = logic.mkBoolVar("a");
    auto idom = getImmediateDominators(a, logic);
    ASSERT_EQ(idom.size(), 1);
    ASSERT_EQ(idom.at(a), a);
}

TEST(Dominators_test, test_Tree)
{
    Logic logic;
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef conj = logic.mkAnd(a,b);
    auto idom = getImmediateDominators(conj, logic);
    ASSERT_EQ(idom.size(), 3);
    ASSERT_EQ(idom.at(a),conj);
    ASSERT_EQ(idom.at(b),conj);
    ASSERT_EQ(idom.at(conj),conj);
}

TEST(Dominators_test, test_SimpleDAG)
{
    Logic logic;
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef conj = logic.mkAnd(a,b);
    PTRef neg = logic.mkNot(a);
    PTRef root = logic.mkOr(neg, conj);
    auto idom = getImmediateDominators(root, logic);
    ASSERT_EQ(idom.size(), 5);
    ASSERT_EQ(idom.at(a),root);
    ASSERT_EQ(idom.at(b),conj);
    ASSERT_EQ(idom.at(conj),root);
    ASSERT_EQ(idom.at(neg),root);
    ASSERT_EQ(idom.at(root),root);
}




