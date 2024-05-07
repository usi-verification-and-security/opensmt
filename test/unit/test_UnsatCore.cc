/*
 *  Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include <ArithLogic.h>
#include <MainSolver.h>
#include <SMTConfig.h>

#include <memory>

/// Pure propositional and uninterpreted functions
class UFUnsatCoreTest : public ::testing::Test {
protected:
    UFUnsatCoreTest(): logic{opensmt::Logic_t::QF_UF} {}
    void SetUp() override {
        ufsort = logic.declareUninterpretedSort("U");
        x = logic.mkVar(ufsort, "x");
        y = logic.mkVar(ufsort, "y");
        f = logic.declareFun("f", ufsort, {ufsort});
        g = logic.declareFun("g", ufsort, {ufsort, ufsort});
        p = logic.declareFun("p", logic.getSort_bool(), {ufsort});
        b1 = logic.mkBoolVar("b1");
        b2 = logic.mkBoolVar("b2");
        b3 = logic.mkBoolVar("b3");
        b4 = logic.mkBoolVar("b4");
        b5 = logic.mkBoolVar("b5");
        nb1 = logic.mkNot(b1);
        nb2 = logic.mkNot(b2);
        nb3 = logic.mkNot(b3);
        nb4 = logic.mkNot(b4);
        nb5 = logic.mkNot(b5);
    }
    Logic logic;
    SMTConfig config;
    SRef ufsort;
    PTRef x, y, b1, b2, b3, b4, b5;
    PTRef nb1, nb2, nb3, nb4, nb5;
    SymRef f, g, p;

    MainSolver makeSolver() {
        const char* msg = "ok";
        config.setOption(SMTConfig::o_produce_unsat_cores, SMTOption(true), msg);
        return {logic, config, "unsat_core"};
    }
};

TEST_F(UFUnsatCoreTest, Bool_Simple) {
    MainSolver solver = makeSolver();
    solver.insertFormula(b1);
    solver.insertFormula(b2);
    solver.insertFormula(nb1);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    ASSERT_EQ(core.size(), 2);
    EXPECT_TRUE(core[0] == b1 or core[1] == b1);
    EXPECT_TRUE(core[0] == nb1 or core[1] == nb1);
}

TEST_F(UFUnsatCoreTest, Bool_ReuseProofChain) {
    // We add three assertions
    // a1 := (b1 or b2) and (b1 or ~b2)
    // a2 := (~b1 or b3) and (~b1 or ~b3)
    // a3 := b4
    // The first two assertions form the unsat core.
    MainSolver solver = makeSolver();
    PTRef c1 = logic.mkOr(b1, b2);
    PTRef c2 = logic.mkOr(b1, nb2);
    PTRef c3 = logic.mkOr(nb1, b3);
    PTRef c4 = logic.mkOr(nb1, nb3);
    PTRef a1 = logic.mkAnd(c1,c2);
    PTRef a2 = logic.mkAnd(c3,c4);
    solver.insertFormula(a1);
    solver.insertFormula(a2);
    solver.insertFormula(b4);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    ASSERT_EQ(core.size(), 2);
    EXPECT_TRUE(core[0] == a1 or core[1] == a1);
    EXPECT_TRUE(core[0] == a2 or core[1] == a2);
}

TEST_F(UFUnsatCoreTest, UF_Simple) {
    // a1 := x = y
    // a2 := g(x,y) = g(y,x)
    // a3 := f(x) != f(y)
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkEq(x,y);
    PTRef a2 = logic.mkEq(logic.mkUninterpFun(g,{x,y}), logic.mkUninterpFun(g,{y,x}));
    PTRef a3 = logic.mkNot(logic.mkEq(logic.mkUninterpFun(f,{x}), logic.mkUninterpFun(f,{y})));
    solver.insertFormula(a1);
    solver.insertFormula(a2);
    solver.insertFormula(a3);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    ASSERT_EQ(core.size(), 2);
    EXPECT_TRUE(core[0] == a1 or core[1] == a1);
    EXPECT_TRUE(core[0] == a3 or core[1] == a3);
}

/// Pure arrays
class AXUnsatCoreTest : public ::testing::Test {
protected:
    AXUnsatCoreTest(): logic{opensmt::Logic_t::QF_AX} {}
    void SetUp() override {
        indexSort = logic.declareUninterpretedSort("Index");
        elementSort = logic.declareUninterpretedSort("Element");
        arraySort = logic.getArraySort(indexSort, elementSort);
        i = logic.mkVar(indexSort, "i");
        j = logic.mkVar(indexSort, "j");
        k = logic.mkVar(indexSort, "k");
        e = logic.mkVar(elementSort, "e");
        a = logic.mkVar(arraySort, "a");
    }
    Logic logic;
    SMTConfig config;
    SRef indexSort;
    SRef elementSort;
    SRef arraySort;
    PTRef i, j, k, e, a;

    MainSolver makeSolver() {
        const char* msg = "ok";
        config.setOption(SMTConfig::o_produce_unsat_cores, SMTOption(true), msg);
        return {logic, config, "unsat_core"};
    }
};

TEST_F(AXUnsatCoreTest, AX_Simple) {
    // a1 := i != j
    // a2 := a[j] != a<i -> e>[j]
    // a3 := a[k] = e
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkNot(logic.mkEq(i,j));
    PTRef a2 = logic.mkNot(logic.mkEq(logic.mkSelect({a,j}), logic.mkSelect({logic.mkStore({a,i,e}),j})));
    PTRef a3 = logic.mkEq(logic.mkSelect({a,k}), e);
    solver.insertFormula(a1);
    solver.insertFormula(a2);
    solver.insertFormula(a3);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    ASSERT_EQ(core.size(), 2);
    auto isInCore = [&](PTRef fla) -> bool { return std::find(core.begin(), core.end(), fla) != core.end(); };
    EXPECT_TRUE(isInCore(a1));
    EXPECT_TRUE(isInCore(a2));
}

/// Linear integer arithmetic
class LIAUnsatCoreTest : public ::testing::Test {
protected:
    LIAUnsatCoreTest(): logic{opensmt::Logic_t::QF_LIA} {}
    void SetUp() override {
        x = logic.mkIntVar("x");
        y = logic.mkIntVar("y");
        z = logic.mkIntVar("z");
        b1 = logic.mkBoolVar("b1");
        b2 = logic.mkBoolVar("b2");
        b3 = logic.mkBoolVar("b3");
        b4 = logic.mkBoolVar("b4");
        b5 = logic.mkBoolVar("b5");
        nb1 = logic.mkNot(b1);
        nb2 = logic.mkNot(b2);
        nb3 = logic.mkNot(b3);
        nb4 = logic.mkNot(b4);
        nb5 = logic.mkNot(b5);
    }
    ArithLogic logic;
    SMTConfig config;
    PTRef x, y, z, b1, b2, b3, b4, b5;
    PTRef nb1, nb2, nb3, nb4, nb5;

    MainSolver makeSolver() {
        const char* msg = "ok";
        config.setOption(SMTConfig::o_produce_unsat_cores, SMTOption(true), msg);
        return {logic, config, "unsat_core"};
    }
};

TEST_F(LIAUnsatCoreTest, LIA_Simple) {
    // a1 := x >= y
    // a2 := y >= z
    // a3 := x + y + z < 0
    // a4 := x < z
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkGeq(x,y);
    PTRef a2 = logic.mkGeq(y,z);
    PTRef a3 = logic.mkLt(logic.mkPlus(vec<PTRef>{x,y,z}), logic.getTerm_IntZero());
    PTRef a4 = logic.mkLt(x,z);
    solver.insertFormula(a1);
    solver.insertFormula(a2);
    solver.insertFormula(a3);
    solver.insertFormula(a4);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    ASSERT_EQ(core.size(), 3);
    auto isInCore = [&](PTRef fla) -> bool { return std::find(core.begin(), core.end(), fla) != core.end(); };
    EXPECT_TRUE(isInCore(a1));
    EXPECT_TRUE(isInCore(a2));
    EXPECT_TRUE(isInCore(a4));
}

/// Arrays + Linear integer arithmetic
class ALIAUnsatCoreTest : public ::testing::Test {
protected:
    ALIAUnsatCoreTest(): logic{opensmt::Logic_t::QF_ALIA} {}
    void SetUp() override {
        intIntArraySort = logic.getArraySort(logic.getSort_int(), logic.getSort_int());
        arr1 = logic.mkVar(intIntArraySort, "a1");
        arr2 = logic.mkVar(intIntArraySort, "a2");
        x = logic.mkIntVar("x");
        y = logic.mkIntVar("y");
        z = logic.mkIntVar("z");
        b1 = logic.mkBoolVar("b1");
        b2 = logic.mkBoolVar("b2");
        b3 = logic.mkBoolVar("b3");
        b4 = logic.mkBoolVar("b4");
        b5 = logic.mkBoolVar("b5");
        nb1 = logic.mkNot(b1);
        nb2 = logic.mkNot(b2);
        nb3 = logic.mkNot(b3);
        nb4 = logic.mkNot(b4);
        nb5 = logic.mkNot(b5);
    }
    ArithLogic logic;
    SMTConfig config;
    SRef intIntArraySort;
    PTRef arr1, arr2;
    PTRef x, y, z, b1, b2, b3, b4, b5;
    PTRef nb1, nb2, nb3, nb4, nb5;

    MainSolver makeSolver() {
        const char* msg = "ok";
        config.setOption(SMTConfig::o_produce_unsat_cores, SMTOption(true), msg);
        return {logic, config, "unsat_core"};
    }
};

TEST_F(ALIAUnsatCoreTest, ALIA_Simple) {
    // a1 := select(arr1, x) != select(arr1,y)
    // a2 := select(arr1, x) == 0
    // a3 := x == y
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkNot(logic.mkEq(logic.mkSelect({arr1, x}), logic.mkSelect({arr1,y})));
    PTRef a2 = logic.mkEq(logic.mkSelect({arr1,x}), logic.getTerm_IntZero());
    PTRef a3 = logic.mkEq(x,y);
    solver.insertFormula(a1);
    solver.insertFormula(a2);
    solver.insertFormula(a3);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    ASSERT_EQ(core.size(), 2);
    auto isInCore = [&](PTRef fla) -> bool { return std::find(core.begin(), core.end(), fla) != core.end(); };
    EXPECT_TRUE(isInCore(a1));
    EXPECT_TRUE(isInCore(a3));
}
