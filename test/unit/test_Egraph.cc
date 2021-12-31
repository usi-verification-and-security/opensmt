/*
 * Copyright (c) 2018-2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include "Egraph.h"
#include "TreeOps.h"

TEST(UseVector_test, testAdd){
    UseVector uv;
    ERef x{0};
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    EXPECT_TRUE(uv[0].isValid());
}

TEST(UseVector_test, testAddAndRemove){
    UseVector uv;
    ERef x{0};
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    uv.clearEntryAt(0);
    ASSERT_EQ(uv.size(), 0);
    auto entry =  uv[0];
    EXPECT_TRUE(entry.isFree());
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    entry = uv[0];
    EXPECT_TRUE(entry.isValid());
}

TEST(UseVector_test, testAddAndRemoveMultiple){
    UseVector uv;
    ERef x{0};
    uv.addParent(x);
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 2);
    uv.clearEntryAt(0);
    ASSERT_EQ(uv.size(), 1);
    uv.clearEntryAt(1);
    ASSERT_EQ(uv.size(), 0);
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 2);
}

TEST(UseVector_test, testWriteRead){
    UseVector uv;
    ERef x{137};
    auto index = uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    auto entry = uv[index];
    ASSERT_EQ(UseVector::entryToERef(entry), x);
    entry.mark();
    entry.unmark();
    ASSERT_EQ(UseVector::entryToERef(entry), x);
}

class EgraphTest: public ::testing::Test {
public:
    Logic logic;
    Egraph egraph;
    SMTConfig c;
    EgraphTest() : logic{opensmt::Logic_t::QF_UF}, egraph(c, logic) {}
};

TEST_F(EgraphTest, test_booleans) {
    PTRef v3 = logic.mkBoolVar("v3");
    PTRef v7 = logic.mkBoolVar("v7");
    SymRef uf3 = logic.declareFun("uf3", logic.getSort_bool(), {logic.getSort_bool()});

    PTRef uf3_v7 = logic.mkUninterpFun(uf3, {v7});
    PTRef uf3_v3 = logic.mkUninterpFun(uf3, {v3}); // Intentionally not declared to egraph
    PTRef eq = logic.mkEq(logic.mkNot(v3), uf3_v7);
    PTRef uf3_eq = logic.mkUninterpFun(uf3, {eq}); // Intentionally not declared to egraph

    AppearsInUfVisitor visitor(logic); // to mark booleans as needed for EGraph
    visitor.visit(uf3_v3);
    visitor.visit(uf3_eq);

    egraph.declareAtom(eq);
    egraph.declareAtom(v3);
    egraph.declareAtom(uf3_v7);

    ASSERT_TRUE(egraph.assertLit({v3, l_True}));
    ASSERT_TRUE(egraph.assertLit({uf3_v7, l_True}));
    ASSERT_FALSE(egraph.assertLit({eq, l_True}));

    vec<PtAsgn> expl;
    egraph.getConflict(expl);

    ASSERT_EQ(expl.size(), 3);
    for (auto pta : expl) {
        bool pta_found = false;
        for (auto pta_ref : vec<PtAsgn>{{v3, l_True}, {uf3_v7, l_True}, {eq, l_True}}) {
            pta_found |= (pta_ref == pta);
        }
        ASSERT_TRUE(pta_found);
    }
}

TEST_F(EgraphTest, test_IncrementalAddition) {
    SRef sref = logic.declareUninterpretedSort("U");
    PTRef x = logic.mkVar(sref, "x");
    PTRef y = logic.mkVar(sref, "y");
    PTRef z = logic.mkVar(sref, "z");
    SymRef f = logic.declareFun("f", sref, {sref});
    PTRef fx = logic.mkUninterpFun(f, {x});
    PTRef fy = logic.mkUninterpFun(f, {y});

    PTRef eq1 = logic.mkEq(fx,fy);

    egraph.declareAtom(eq1);
    egraph.pushBacktrackPoint();
    ASSERT_TRUE(egraph.assertLit({eq1, l_False}));
    ASSERT_EQ(egraph.check(true), TRes::SAT);

    PTRef eq2 = logic.mkEq(x,z);
    egraph.declareAtom(eq2);
    egraph.pushBacktrackPoint();
    ASSERT_TRUE(egraph.assertLit({eq2, l_True}));
    ASSERT_EQ(egraph.check(true), TRes::SAT);

    PTRef eq3 = logic.mkEq(y,z);
    egraph.declareAtom(eq3);
    egraph.pushBacktrackPoint();
    ASSERT_FALSE(egraph.assertLit({eq3, l_True}));

    egraph.popBacktrackPoint();
    egraph.popBacktrackPoint();

    egraph.pushBacktrackPoint();
    ASSERT_TRUE(egraph.assertLit({eq2, l_False}));

    egraph.pushBacktrackPoint();
    ASSERT_TRUE(egraph.assertLit({eq3, l_True}));
    ASSERT_EQ(egraph.check(true), TRes::SAT);
}
