//
// Created by Martin Blicha on 2018-12-31.
//

#include <gtest/gtest.h>
#include "Egraph.h"

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
    EgraphTest() : logic{}, egraph(c, logic) {}
};

TEST_F(EgraphTest, test_booleans) {
    PTRef v3 = logic.mkBoolVar("v3");
    PTRef v7 = logic.mkBoolVar("v7");
    SymRef uf3 = logic.declareFun("uf3", logic.getSort_bool(), {logic.getSort_bool()}, nullptr);

    PTRef uf3_v7 = logic.mkUninterpFun(uf3, {v7});
    PTRef uf3_v3 = logic.mkUninterpFun(uf3, {v3}); // Intentionally not declared to egraph
    PTRef eq = logic.mkEq(logic.mkNot(v3), uf3_v7);
    PTRef uf3_eq = logic.mkUninterpFun(uf3, {eq}); // Intentionally not declared to egraph
    egraph.declareAtom(eq);
    egraph.declareAtom(v3);
    egraph.declareAtom(uf3_v7);

    ASSERT_TRUE(egraph.assertLit({v3, l_True}));
    ASSERT_TRUE(egraph.assertLit({uf3_v7, l_True}));
    ASSERT_FALSE(egraph.assertLit({eq, l_True}));

    vec<PtAsgn> expl;
    egraph.getConflict(false, expl);

    ASSERT_EQ(expl.size(), 3);
    for (auto pta : expl) {
        bool pta_found = false;
        for (auto pta_ref : vec<PtAsgn>{{v3, l_True}, {uf3_v7, l_True}, {eq, l_True}}) {
            pta_found |= (pta_ref == pta);
        }
        ASSERT_TRUE(pta_found);
    }
}
