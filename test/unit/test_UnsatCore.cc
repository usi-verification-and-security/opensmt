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
