//
// Created by prova on 20.10.20.
//

#include <gtest/gtest.h>
#include <Logic.h>
#include <EnodeStore.h>
#include <TreeOps.h>

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
    AppearsInUfVisitor(logic).visit(P_A);
    EnodeStore enodeStore(logic);
    for (auto tr : {B, conj}) {
        // No enode needed: B is a boolean atom not appearing in UF, and conj is a boolean operator not appearing in UF
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }
    for (auto tr: {A, P_A}) {
        // Enode is needed: A appears in P_A and P_A is an uninterpreted predicate
        ASSERT_TRUE(enodeStore.needsEnode(tr));
    }
}

TEST_F(EnodeStoreTest, testUPWithInternalConjIncr) {
    PTRef A = logic.mkBoolVar("A");
    PTRef B = logic.mkBoolVar("B");
    EnodeStore enodeStore(logic);
    for (auto tr : {A, B}) {
        // No enode needed: A and B are boolean predicates not appearing in UF
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }
    PTRef conj = logic.mkAnd({A, B});
    // No enode needed: conj is a boolean operator not appearing in UF
    ASSERT_FALSE(enodeStore.needsEnode(conj));

    PTRef P_conj = logic.mkUninterpFun(logic.declareFun("P", logic.getSort_bool(), {logic.getSort_bool()}, nullptr), {conj});
    AppearsInUfVisitor(logic).visit(P_conj);
    // Enode needed: P is a UP
    ASSERT_TRUE(enodeStore.needsEnode(P_conj));
    // Enode needed: conj appears in a UP
    ASSERT_TRUE(enodeStore.needsEnode(conj));
    for (auto tr : {A, B}) {
        // No enode needed: A and B appear in conj, but not directly in P.
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }

    PTRef Q_A = logic.mkUninterpFun(logic.declareFun("Q", logic.getSort_bool(), {logic.getSort_bool()}, nullptr), {A});
    AppearsInUfVisitor(logic).visit(Q_A);
    for (auto tr : {A, conj, Q_A}) {
        // Enode needed: A appears in the UP Q, conj still appears in P, Q_A is a UP
        ASSERT_TRUE(enodeStore.needsEnode(tr));
    }
    // No enode needed: B appears only in conj, but not directly in a UF
    ASSERT_FALSE(enodeStore.needsEnode(B)); // Needs to be local
}


TEST_F(EnodeStoreTest, testUFEquality) {
    PTRef x = logic.mkBoolVar("x");
    PTRef y = logic.mkBoolVar("y");
    PTRef eq = logic.mkEq(x, y);
    EnodeStore enodeStore(logic);
    for (auto tr : {x, y, eq}) {
        // No enode: x, y, and eq are booleans not appearing in UF
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }
    PTRef f = logic.mkUninterpFun(logic.declareFun("f", logic.getSort_bool(), {logic.getSort_bool()}, nullptr), {eq});
    AppearsInUfVisitor(logic).visit(f);
    for (auto tr : {f, eq}) {
        // Enodes needed: f is a UP and eq appears in f
        ASSERT_TRUE(enodeStore.needsEnode(tr));
    }

    for (auto tr : {x, y}) {
        // No enodes needed: x and y do not appear directly in a UF
        ASSERT_FALSE(enodeStore.needsEnode(tr));
    }
}

TEST_F(EnodeStoreTest, testUFMixed) {
    PTRef x = logic.mkBoolVar("x");
    EnodeStore enodeStore(logic);
    // No enode needed: x is a boolean var not apparing in UF
    ASSERT_FALSE(enodeStore.needsEnode(x));
    SRef ufsort = logic.declareSort("U", nullptr);
    PTRef a = logic.mkUninterpFun(logic.declareFun("a", ufsort, {}, nullptr), {});
    PTRef mixed = logic.mkUninterpFun(logic.declareFun("P", logic.getSort_bool(), {ufsort, logic.getSort_bool()}, nullptr), {x, a});
    AppearsInUfVisitor(logic).visit(mixed);
    // Enode needed: a is a UF, mixed is a UP, and x appears in mixed
    ASSERT_TRUE(enodeStore.needsEnode(a));
    ASSERT_TRUE(enodeStore.needsEnode(mixed));
    ASSERT_TRUE(enodeStore.needsEnode(x));
}