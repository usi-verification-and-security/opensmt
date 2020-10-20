//
// Created by prova on 20.10.20.
//

#include <gtest/gtest.h>
#include <Logic.h>
#include <EnodeStore.h>

class EnodeStoreTest : public ::testing::Test {
protected:
    Logic logic;
    EnodeStoreTest() {}
};

TEST_F(EnodeStoreTest, testUP) {
    PTRef A = logic.mkBoolVar("A");
    PTRef B = logic.mkBoolVar("B");
    PTRef conj = logic.mkAnd({A, B});
    PTRef P_A = logic.mkUninterpFun(logic.declareFun("P", logic.getSort_bool(), {logic.getSort_bool()}, nullptr), {A});
    EnodeStore enodeStore(logic);
    for (auto tr : {B, conj}) {
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }
    for (auto tr: {A, P_A}) {
        ASSERT_TRUE(enodeStore.needsEnode(tr));
    }
}

TEST_F(EnodeStoreTest, testUPWithInternalConjIncr) {
    PTRef A = logic.mkBoolVar("A");
    PTRef B = logic.mkBoolVar("B");
    EnodeStore enodeStore(logic);
    for (auto tr : {A, B}) {
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }
    PTRef conj = logic.mkAnd({A, B});
    ASSERT_FALSE(enodeStore.needsEnode(conj));

    PTRef P_conj = logic.mkUninterpFun(logic.declareFun("P", logic.getSort_bool(), {logic.getSort_bool()}, nullptr), {conj});
    ASSERT_TRUE(enodeStore.needsEnode(P_conj));
    ASSERT_TRUE(enodeStore.needsEnode(conj));
    for (auto tr : {A, B}) {
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }

    PTRef Q_A = logic.mkUninterpFun(logic.declareFun("Q", logic.getSort_bool(), {logic.getSort_bool()}, nullptr), {A});
    for (auto tr : {A, conj, Q_A}) {
        ASSERT_TRUE(enodeStore.needsEnode(tr));
    }
    ASSERT_FALSE(enodeStore.needsEnode(B)); // Needs to be local
}


TEST_F(EnodeStoreTest, testUFEquality) {
    PTRef x = logic.mkBoolVar("x");
    PTRef y = logic.mkBoolVar("y");
    PTRef eq = logic.mkEq(x, y);
    EnodeStore enodeStore(logic);
    for (auto tr : {x, y, eq}) {
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }
    PTRef f = logic.mkUninterpFun(logic.declareFun("f", logic.getSort_bool(), {logic.getSort_bool()}, nullptr), {eq});

    for (auto tr : {f, eq}) {
        ASSERT_TRUE(enodeStore.needsEnode(tr));
    }

    for (auto tr : {x, y}) {
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }
}

TEST_F(EnodeStoreTest, testUFMixed) {
    PTRef x = logic.mkBoolVar("x");
    EnodeStore enodeStore(logic);
    ASSERT_FALSE(enodeStore.needsEnode(x));
    SRef ufsort = logic.declareSort("U", nullptr);
    PTRef a = logic.mkUninterpFun(logic.declareFun("a", ufsort, {}, nullptr), {});
    PTRef mixed = logic.mkUninterpFun(logic.declareFun("P", logic.getSort_bool(), {ufsort, logic.getSort_bool()}, nullptr), {x, a});
    ASSERT_TRUE(enodeStore.needsEnode(a));
    ASSERT_TRUE(enodeStore.needsEnode(mixed));
    ASSERT_TRUE(enodeStore.needsEnode(x));
}