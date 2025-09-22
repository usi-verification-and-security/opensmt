/*
 *  Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

// The tests should ideally cover also UnsatCoreBuilder itself

#include <gtest/gtest.h>
#include <logics/ArithLogic.h>
#include <api/MainSolver.h>
#include <options/SMTConfig.h>
#include <unsatcores/UnsatCore.h>

#include <memory>

namespace opensmt {

bool isInCore(PTRef fla, vec<PTRef> const & coreTerms) {
    return std::find(coreTerms.begin(), coreTerms.end(), fla) != coreTerms.end();
}

bool isNameInCore(TermName const & name, std::vector<std::string> const & coreNames) {
    return std::find(coreNames.begin(), coreNames.end(), name) != coreNames.end();
}

template <typename LogicT>
class UnsatCoreTestBase {
protected:
    UnsatCoreTestBase(Logic_t type) : logic{type} {}

    LogicT logic;
    SMTConfig config;

    MainSolver makeSolver() {
        const char* msg = "ok";
        config.setOption(SMTConfig::o_produce_unsat_cores, SMTOption(true), msg);
        return {logic, config, "unsat_core"};
    }
};

template <typename LogicT>
class MinUnsatCoreTestBase {
protected:
    MinUnsatCoreTestBase(Logic_t type) : logic{type} {}

    LogicT logic;
    SMTConfig config;

    MainSolver makeSolver() {
        const char* msg = "ok";
        config.setOption(SMTConfig::o_produce_unsat_cores, SMTOption(true), msg);
        config.setOption(SMTConfig::o_minimal_unsat_cores, SMTOption(true), msg);
        return {logic, config, "unsat_core"};
    }
};

template <typename LogicT>
class FullUnsatCoreTestBase {
protected:
    FullUnsatCoreTestBase(Logic_t type) : logic{type} {}

    LogicT logic;
    SMTConfig config;

    MainSolver makeSolver() {
        const char* msg = "ok";
        config.setOption(SMTConfig::o_produce_unsat_cores, SMTOption(true), msg);
        config.setOption(SMTConfig::o_print_cores_full, SMTOption(true), msg);
        return {logic, config, "unsat_core"};
    }
};

template <typename LogicT>
class MinFullUnsatCoreTestBase {
protected:
    MinFullUnsatCoreTestBase(Logic_t type) : logic{type} {}

    LogicT logic;
    SMTConfig config;

    MainSolver makeSolver() {
        const char* msg = "ok";
        config.setOption(SMTConfig::o_produce_unsat_cores, SMTOption(true), msg);
        config.setOption(SMTConfig::o_print_cores_full, SMTOption(true), msg);
        config.setOption(SMTConfig::o_minimal_unsat_cores, SMTOption(true), msg);
        return {logic, config, "unsat_core"};
    }
};

/// Pure propositional and uninterpreted functions
template <template<typename> typename TestBaseT>
class UFUnsatCoreTestTp : public ::testing::Test, public TestBaseT<Logic> {
protected:
    using Base = TestBaseT<Logic>;
    using Base::logic;

    UFUnsatCoreTestTp() : Base(Logic_t::QF_UF) {}
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
    SRef ufsort;
    PTRef x, y, b1, b2, b3, b4, b5;
    PTRef nb1, nb2, nb3, nb4, nb5;
    SymRef f, g, p;
};

using UFUnsatCoreTest = UFUnsatCoreTestTp<UnsatCoreTestBase>;
using MinUFUnsatCoreTest = UFUnsatCoreTestTp<MinUnsatCoreTestBase>;
using FullUFUnsatCoreTest = UFUnsatCoreTestTp<FullUnsatCoreTestBase>;
using MinFullUFUnsatCoreTest = UFUnsatCoreTestTp<MinFullUnsatCoreTestBase>;

TEST_F(UFUnsatCoreTest, Bool_Simple) {
    MainSolver solver = makeSolver();
    solver.tryAddNamedAssertion(b1, "a1");
    solver.tryAddNamedAssertion(b2, "a2");
    solver.tryAddNamedAssertion(nb1, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_TRUE(isInCore(nb1, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 2);
    EXPECT_TRUE(isNameInCore("a1", coreNames));
    EXPECT_FALSE(isNameInCore("a2", coreNames));
    EXPECT_TRUE(isNameInCore("a3", coreNames));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Simple) {
    MainSolver solver = makeSolver();
    solver.tryAddNamedAssertion(b1, "a1");
    solver.tryAddNamedAssertion(b2, "a2");
    solver.tryAddNamedAssertion(nb1, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_TRUE(isInCore(nb1, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 2);
    EXPECT_TRUE(isNameInCore("a1", coreNames));
    EXPECT_FALSE(isNameInCore("a2", coreNames));
    EXPECT_TRUE(isNameInCore("a3", coreNames));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Simple_Unnamed1) {
    MainSolver solver = makeSolver();
    solver.addAssertion(b1);
    solver.tryAddNamedAssertion(b2, "a2");
    solver.tryAddNamedAssertion(nb1, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_FALSE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_TRUE(isInCore(nb1, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 1);
    EXPECT_FALSE(isNameInCore("a1", coreNames));
    EXPECT_FALSE(isNameInCore("a2", coreNames));
    EXPECT_TRUE(isNameInCore("a3", coreNames));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Simple_Unnamed2) {
    MainSolver solver = makeSolver();
    solver.tryAddNamedAssertion(b1, "a1");
    solver.addAssertion(b2);
    solver.tryAddNamedAssertion(nb1, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_TRUE(isInCore(nb1, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 2);
    EXPECT_TRUE(isNameInCore("a1", coreNames));
    EXPECT_FALSE(isNameInCore("a2", coreNames));
    EXPECT_TRUE(isNameInCore("a3", coreNames));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Simple_Unnamed3) {
    MainSolver solver = makeSolver();
    solver.tryAddNamedAssertion(b1, "a1");
    solver.tryAddNamedAssertion(b2, "a2");
    solver.addAssertion(nb1);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_TRUE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_FALSE(isInCore(nb1, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 1);
    EXPECT_TRUE(isNameInCore("a1", coreNames));
    EXPECT_FALSE(isNameInCore("a2", coreNames));
    EXPECT_FALSE(isNameInCore("a3", coreNames));
}

TEST_F(FullUFUnsatCoreTest, Full_Bool_Simple) {
    MainSolver solver = makeSolver();
    solver.addAssertion(b1);
    solver.addAssertion(b2);
    solver.addAssertion(nb1);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_TRUE(isInCore(nb1, coreTerms));
}

TEST_F(MinFullUFUnsatCoreTest, Min_Full_Bool_Simple) {
    MainSolver solver = makeSolver();
    solver.addAssertion(b1);
    solver.addAssertion(b2);
    solver.addAssertion(nb1);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_TRUE(isInCore(nb1, coreTerms));
}

TEST_F(MinFullUFUnsatCoreTest, Min_Full_Bool_Simple_Unnamed1) {
    MainSolver solver = makeSolver();
    solver.addAssertion(b1);
    solver.tryAddNamedAssertion(b2, "a2");
    solver.tryAddNamedAssertion(nb1, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_TRUE(isInCore(nb1, coreTerms));
}

TEST_F(MinFullUFUnsatCoreTest, Min_Full_Bool_Simple_Unnamed2) {
    MainSolver solver = makeSolver();
    solver.tryAddNamedAssertion(b1, "a1");
    solver.addAssertion(b2);
    solver.tryAddNamedAssertion(nb1, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_TRUE(isInCore(nb1, coreTerms));
}

TEST_F(MinFullUFUnsatCoreTest, Min_Full_Bool_Simple_Unnamed3) {
    MainSolver solver = makeSolver();
    solver.tryAddNamedAssertion(b1, "a1");
    solver.tryAddNamedAssertion(b2, "a2");
    solver.addAssertion(nb1);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(b1, coreTerms));
    EXPECT_FALSE(isInCore(b2, coreTerms));
    EXPECT_TRUE(isInCore(nb1, coreTerms));
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
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(b4, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(b4, coreTerms));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_ReuseProofChain) {
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
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(b4, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(b4, coreTerms));
}

TEST_F(FullUFUnsatCoreTest, Full_Bool_ReuseProofChain) {
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
    solver.addAssertion(a1);
    solver.addAssertion(a2);
    solver.addAssertion(b4);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(b4, coreTerms));
}

TEST_F(UFUnsatCoreTest, Bool_Trivial_ITE) {
    MainSolver solver = makeSolver();
    PTRef ite = logic.mkIte(b1, nb1, b1);
    solver.tryAddNamedAssertion(ite, "a");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_TRUE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 1);
    EXPECT_TRUE(isNameInCore("a", coreNames));
}

TEST_F(UFUnsatCoreTest, Bool_Trivial_ITE_Unnamed) {
    MainSolver solver = makeSolver();
    PTRef ite = logic.mkIte(b1, nb1, b1);
    solver.addAssertion(ite);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 0);
    EXPECT_FALSE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 0);
    EXPECT_FALSE(isNameInCore("a", coreNames));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Trivial_ITE) {
    MainSolver solver = makeSolver();
    PTRef ite = logic.mkIte(b1, nb1, b1);
    solver.tryAddNamedAssertion(ite, "a");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_TRUE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 1);
    EXPECT_TRUE(isNameInCore("a", coreNames));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Trivial_ITE_Unnamed) {
    MainSolver solver = makeSolver();
    PTRef ite = logic.mkIte(b1, nb1, b1);
    solver.addAssertion(ite);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 0);
    EXPECT_FALSE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 0);
    EXPECT_FALSE(isNameInCore("a", coreNames));
}

TEST_F(FullUFUnsatCoreTest, Full_Bool_Trivial_ITE) {
    MainSolver solver = makeSolver();
    PTRef ite = logic.mkIte(b1, nb1, b1);
    solver.addAssertion(ite);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_TRUE(isInCore(ite, coreTerms));
}

TEST_F(UFUnsatCoreTest, Bool_Simple_ITE) {
    MainSolver solver = makeSolver();
    PTRef eq = logic.mkEq(b1, b2);
    PTRef impl1 = logic.mkImpl(b1, b2);
    PTRef impl2 = logic.mkImpl(b2, b1);
    PTRef nimpl1 = logic.mkNot(impl1);
    PTRef nimpl2 = logic.mkNot(impl2);
    PTRef ite = logic.mkIte(b3, nimpl1, nimpl2);
    solver.tryAddNamedAssertion(eq, "a1");
    solver.tryAddNamedAssertion(ite, "a2");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(eq, coreTerms));
    EXPECT_TRUE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 2);
    EXPECT_TRUE(isNameInCore("a1", coreNames));
    EXPECT_TRUE(isNameInCore("a2", coreNames));
}

TEST_F(UFUnsatCoreTest, Bool_Simple_ITE_Unnamed1) {
    MainSolver solver = makeSolver();
    PTRef eq = logic.mkEq(b1, b2);
    PTRef impl1 = logic.mkImpl(b1, b2);
    PTRef impl2 = logic.mkImpl(b2, b1);
    PTRef nimpl1 = logic.mkNot(impl1);
    PTRef nimpl2 = logic.mkNot(impl2);
    PTRef ite = logic.mkIte(b3, nimpl1, nimpl2);
    solver.addAssertion(eq);
    solver.tryAddNamedAssertion(ite, "a2");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_FALSE(isInCore(eq, coreTerms));
    EXPECT_TRUE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 1);
    EXPECT_FALSE(isNameInCore("a1", coreNames));
    EXPECT_TRUE(isNameInCore("a2", coreNames));
}

TEST_F(UFUnsatCoreTest, Bool_Simple_ITE_Unnamed2) {
    MainSolver solver = makeSolver();
    PTRef eq = logic.mkEq(b1, b2);
    PTRef impl1 = logic.mkImpl(b1, b2);
    PTRef impl2 = logic.mkImpl(b2, b1);
    PTRef nimpl1 = logic.mkNot(impl1);
    PTRef nimpl2 = logic.mkNot(impl2);
    PTRef ite = logic.mkIte(b3, nimpl1, nimpl2);
    solver.tryAddNamedAssertion(eq, "a1");
    solver.addAssertion(ite);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_TRUE(isInCore(eq, coreTerms));
    EXPECT_FALSE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 1);
    EXPECT_TRUE(isNameInCore("a1", coreNames));
    EXPECT_FALSE(isNameInCore("a2", coreNames));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Simple_ITE) {
    MainSolver solver = makeSolver();
    PTRef eq = logic.mkEq(b1, b2);
    PTRef impl1 = logic.mkImpl(b1, b2);
    PTRef impl2 = logic.mkImpl(b2, b1);
    PTRef nimpl1 = logic.mkNot(impl1);
    PTRef nimpl2 = logic.mkNot(impl2);
    PTRef ite = logic.mkIte(b3, nimpl1, nimpl2);
    solver.tryAddNamedAssertion(eq, "a1");
    solver.tryAddNamedAssertion(ite, "a2");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(eq, coreTerms));
    EXPECT_TRUE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 2);
    EXPECT_TRUE(isNameInCore("a1", coreNames));
    EXPECT_TRUE(isNameInCore("a2", coreNames));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Simple_ITE_Unnamed1) {
    MainSolver solver = makeSolver();
    PTRef eq = logic.mkEq(b1, b2);
    PTRef impl1 = logic.mkImpl(b1, b2);
    PTRef impl2 = logic.mkImpl(b2, b1);
    PTRef nimpl1 = logic.mkNot(impl1);
    PTRef nimpl2 = logic.mkNot(impl2);
    PTRef ite = logic.mkIte(b3, nimpl1, nimpl2);
    solver.addAssertion(eq);
    solver.tryAddNamedAssertion(ite, "a2");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_FALSE(isInCore(eq, coreTerms));
    EXPECT_TRUE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 1);
    EXPECT_FALSE(isNameInCore("a1", coreNames));
    EXPECT_TRUE(isNameInCore("a2", coreNames));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Simple_ITE_Unnamed2) {
    MainSolver solver = makeSolver();
    PTRef eq = logic.mkEq(b1, b2);
    PTRef impl1 = logic.mkImpl(b1, b2);
    PTRef impl2 = logic.mkImpl(b2, b1);
    PTRef nimpl1 = logic.mkNot(impl1);
    PTRef nimpl2 = logic.mkNot(impl2);
    PTRef ite = logic.mkIte(b3, nimpl1, nimpl2);
    solver.tryAddNamedAssertion(eq, "a1");
    solver.addAssertion(ite);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_TRUE(isInCore(eq, coreTerms));
    EXPECT_FALSE(isInCore(ite, coreTerms));
    auto const & namedCore = static_cast<NamedUnsatCore &>(*core);
    auto coreNames = namedCore.makeTermNames();
    ASSERT_EQ(coreNames.size(), 1);
    EXPECT_TRUE(isNameInCore("a1", coreNames));
    EXPECT_FALSE(isNameInCore("a2", coreNames));
}

TEST_F(FullUFUnsatCoreTest, Full_Bool_Simple_ITE) {
    MainSolver solver = makeSolver();
    PTRef eq = logic.mkEq(b1, b2);
    PTRef impl1 = logic.mkImpl(b1, b2);
    PTRef impl2 = logic.mkImpl(b2, b1);
    PTRef nimpl1 = logic.mkNot(impl1);
    PTRef nimpl2 = logic.mkNot(impl2);
    PTRef ite = logic.mkIte(b3, nimpl1, nimpl2);
    solver.addAssertion(eq);
    solver.addAssertion(ite);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(eq, coreTerms));
    EXPECT_TRUE(isInCore(ite, coreTerms));
}

TEST_F(UFUnsatCoreTest, UF_Simple) {
    // a1 := x = y
    // a2 := g(x,y) = g(y,x)
    // a3 := f(x) != f(y)
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkEq(x,y);
    PTRef a2 = logic.mkEq(logic.mkUninterpFun(g,{x,y}), logic.mkUninterpFun(g,{y,x}));
    PTRef a3 = logic.mkNot(logic.mkEq(logic.mkUninterpFun(f,{x}), logic.mkUninterpFun(f,{y})));
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_FALSE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

TEST_F(MinUFUnsatCoreTest, Min_UF_Simple) {
    // a1 := x = y
    // a2 := g(x,y) = g(y,x)
    // a3 := f(x) != f(y)
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkEq(x,y);
    PTRef a2 = logic.mkEq(logic.mkUninterpFun(g,{x,y}), logic.mkUninterpFun(g,{y,x}));
    PTRef a3 = logic.mkNot(logic.mkEq(logic.mkUninterpFun(f,{x}), logic.mkUninterpFun(f,{y})));
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_FALSE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

TEST_F(MinUFUnsatCoreTest, Min_UF_Simple_Unnamed1) {
    // a1 := x = y
    // a2 := g(x,y) = g(y,x)
    // a3 := f(x) != f(y)
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkEq(x,y);
    PTRef a2 = logic.mkEq(logic.mkUninterpFun(g,{x,y}), logic.mkUninterpFun(g,{y,x}));
    PTRef a3 = logic.mkNot(logic.mkEq(logic.mkUninterpFun(f,{x}), logic.mkUninterpFun(f,{y})));
    solver.addAssertion(a1);
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_FALSE(isInCore(a1, coreTerms));
    EXPECT_FALSE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

TEST_F(MinUFUnsatCoreTest, Min_UF_Simple_Unnamed2) {
    // a1 := x = y
    // a2 := g(x,y) = g(y,x)
    // a3 := f(x) != f(y)
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkEq(x,y);
    PTRef a2 = logic.mkEq(logic.mkUninterpFun(g,{x,y}), logic.mkUninterpFun(g,{y,x}));
    PTRef a3 = logic.mkNot(logic.mkEq(logic.mkUninterpFun(f,{x}), logic.mkUninterpFun(f,{y})));
    solver.tryAddNamedAssertion(a1, "a1");
    solver.addAssertion(a2);
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_FALSE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

TEST_F(MinUFUnsatCoreTest, Min_UF_Simple_Unnamed3) {
    // a1 := x = y
    // a2 := g(x,y) = g(y,x)
    // a3 := f(x) != f(y)
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkEq(x,y);
    PTRef a2 = logic.mkEq(logic.mkUninterpFun(g,{x,y}), logic.mkUninterpFun(g,{y,x}));
    PTRef a3 = logic.mkNot(logic.mkEq(logic.mkUninterpFun(f,{x}), logic.mkUninterpFun(f,{y})));
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.addAssertion(a3);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 1);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_FALSE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(a3, coreTerms));
}

TEST_F(FullUFUnsatCoreTest, Full_UF_Simple) {
    // a1 := x = y
    // a2 := g(x,y) = g(y,x)
    // a3 := f(x) != f(y)
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkEq(x,y);
    PTRef a2 = logic.mkEq(logic.mkUninterpFun(g,{x,y}), logic.mkUninterpFun(g,{y,x}));
    PTRef a3 = logic.mkNot(logic.mkEq(logic.mkUninterpFun(f,{x}), logic.mkUninterpFun(f,{y})));
    solver.addAssertion(a1);
    solver.addAssertion(a2);
    solver.addAssertion(a3);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_FALSE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

TEST_F(UFUnsatCoreTest, Bool_Simple_Overlap) {
    MainSolver solver = makeSolver();
    PTRef a1 = b1;
    PTRef a2 = logic.mkAnd(b1, b2);
    PTRef a3 = logic.mkOr(logic.mkNot(b1), logic.mkNot(b2));
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 3);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

TEST_F(MinUFUnsatCoreTest, Min_Bool_Simple_Overlap) {
    MainSolver solver = makeSolver();
    PTRef a1 = b1;
    PTRef a2 = logic.mkAnd(b1, b2);
    PTRef a3 = logic.mkOr(logic.mkNot(b1), logic.mkNot(b2));
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_FALSE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

TEST_F(FullUFUnsatCoreTest, Full_Bool_Simple_Overlap) {
    MainSolver solver = makeSolver();
    PTRef a1 = b1;
    PTRef a2 = logic.mkAnd(b1, b2);
    PTRef a3 = logic.mkOr(logic.mkNot(b1), logic.mkNot(b2));
    solver.addAssertion(a1);
    solver.addAssertion(a2);
    solver.addAssertion(a3);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 3);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

/// Pure arrays
template <template<typename> typename TestBaseT>
class AXUnsatCoreTestTp : public ::testing::Test, public TestBaseT<Logic> {
protected:
    using Base = TestBaseT<Logic>;
    using Base::logic;

    AXUnsatCoreTestTp() : Base(Logic_t::QF_AX) {}
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
    SRef indexSort;
    SRef elementSort;
    SRef arraySort;
    PTRef i, j, k, e, a;
};

using AXUnsatCoreTest = AXUnsatCoreTestTp<UnsatCoreTestBase>;
using MinAXUnsatCoreTest = AXUnsatCoreTestTp<MinUnsatCoreTestBase>;
using FullAXUnsatCoreTest = AXUnsatCoreTestTp<FullUnsatCoreTestBase>;

TEST_F(AXUnsatCoreTest, AX_Simple) {
    // a1 := i != j
    // a2 := a[j] != a<i -> e>[j]
    // a3 := a[k] = e
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkNot(logic.mkEq(i,j));
    PTRef a2 = logic.mkNot(logic.mkEq(logic.mkSelect({a,j}), logic.mkSelect({logic.mkStore({a,i,e}),j})));
    PTRef a3 = logic.mkEq(logic.mkSelect({a,k}), e);
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(a3, coreTerms));
}

TEST_F(AXUnsatCoreTest, Min_AX_Simple) {
    // a1 := i != j
    // a2 := a[j] != a<i -> e>[j]
    // a3 := a[k] = e
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkNot(logic.mkEq(i,j));
    PTRef a2 = logic.mkNot(logic.mkEq(logic.mkSelect({a,j}), logic.mkSelect({logic.mkStore({a,i,e}),j})));
    PTRef a3 = logic.mkEq(logic.mkSelect({a,k}), e);
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(a3, coreTerms));
}

TEST_F(FullAXUnsatCoreTest, Full_AX_Simple) {
    // a1 := i != j
    // a2 := a[j] != a<i -> e>[j]
    // a3 := a[k] = e
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkNot(logic.mkEq(i,j));
    PTRef a2 = logic.mkNot(logic.mkEq(logic.mkSelect({a,j}), logic.mkSelect({logic.mkStore({a,i,e}),j})));
    PTRef a3 = logic.mkEq(logic.mkSelect({a,k}), e);
    solver.addAssertion(a1);
    solver.addAssertion(a2);
    solver.addAssertion(a3);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(a3, coreTerms));
}


/// Linear integer arithmetic
template <template<typename> typename TestBaseT>
class LIAUnsatCoreTestTp : public ::testing::Test, public TestBaseT<ArithLogic> {
protected:
    using Base = TestBaseT<ArithLogic>;
    using Base::logic;

    LIAUnsatCoreTestTp() : Base(Logic_t::QF_LIA) {}
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
    PTRef x, y, z, b1, b2, b3, b4, b5;
    PTRef nb1, nb2, nb3, nb4, nb5;
};

using LIAUnsatCoreTest = LIAUnsatCoreTestTp<UnsatCoreTestBase>;
using MinLIAUnsatCoreTest = LIAUnsatCoreTestTp<MinUnsatCoreTestBase>;
using FullLIAUnsatCoreTest = LIAUnsatCoreTestTp<FullUnsatCoreTestBase>;

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
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    solver.tryAddNamedAssertion(a4, "a4");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 3);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(a3, coreTerms));
    EXPECT_TRUE(isInCore(a4, coreTerms));
}

TEST_F(LIAUnsatCoreTest, Min_LIA_Simple) {
    // a1 := x >= y
    // a2 := y >= z
    // a3 := x + y + z < 0
    // a4 := x < z
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkGeq(x,y);
    PTRef a2 = logic.mkGeq(y,z);
    PTRef a3 = logic.mkLt(logic.mkPlus(vec<PTRef>{x,y,z}), logic.getTerm_IntZero());
    PTRef a4 = logic.mkLt(x,z);
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    solver.tryAddNamedAssertion(a4, "a4");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 3);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(a3, coreTerms));
    EXPECT_TRUE(isInCore(a4, coreTerms));
}

TEST_F(FullLIAUnsatCoreTest, Full_LIA_Simple) {
    // a1 := x >= y
    // a2 := y >= z
    // a3 := x + y + z < 0
    // a4 := x < z
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkGeq(x,y);
    PTRef a2 = logic.mkGeq(y,z);
    PTRef a3 = logic.mkLt(logic.mkPlus(vec<PTRef>{x,y,z}), logic.getTerm_IntZero());
    PTRef a4 = logic.mkLt(x,z);
    solver.addAssertion(a1);
    solver.addAssertion(a2);
    solver.addAssertion(a3);
    solver.addAssertion(a4);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 3);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_TRUE(isInCore(a2, coreTerms));
    EXPECT_FALSE(isInCore(a3, coreTerms));
    EXPECT_TRUE(isInCore(a4, coreTerms));
}

/// Arrays + Linear integer arithmetic
template <template<typename> typename TestBaseT>
class ALIAUnsatCoreTestTp : public ::testing::Test, public TestBaseT<ArithLogic> {
protected:
    using Base = TestBaseT<ArithLogic>;
    using Base::logic;

    ALIAUnsatCoreTestTp() : Base(Logic_t::QF_ALIA) {}
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
    SRef intIntArraySort;
    PTRef arr1, arr2;
    PTRef x, y, z, b1, b2, b3, b4, b5;
    PTRef nb1, nb2, nb3, nb4, nb5;
};

using ALIAUnsatCoreTest = ALIAUnsatCoreTestTp<UnsatCoreTestBase>;
using MinALIAUnsatCoreTest = ALIAUnsatCoreTestTp<MinUnsatCoreTestBase>;
using FullALIAUnsatCoreTest = ALIAUnsatCoreTestTp<FullUnsatCoreTestBase>;

TEST_F(ALIAUnsatCoreTest, ALIA_Simple) {
    // a1 := select(arr1, x) != select(arr1,y)
    // a2 := select(arr1, x) == 0
    // a3 := x == y
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkNot(logic.mkEq(logic.mkSelect({arr1, x}), logic.mkSelect({arr1,y})));
    PTRef a2 = logic.mkEq(logic.mkSelect({arr1,x}), logic.getTerm_IntZero());
    PTRef a3 = logic.mkEq(x,y);
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_FALSE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

TEST_F(ALIAUnsatCoreTest, Min_ALIA_Simple) {
    // a1 := select(arr1, x) != select(arr1,y)
    // a2 := select(arr1, x) == 0
    // a3 := x == y
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkNot(logic.mkEq(logic.mkSelect({arr1, x}), logic.mkSelect({arr1,y})));
    PTRef a2 = logic.mkEq(logic.mkSelect({arr1,x}), logic.getTerm_IntZero());
    PTRef a3 = logic.mkEq(x,y);
    solver.tryAddNamedAssertion(a1, "a1");
    solver.tryAddNamedAssertion(a2, "a2");
    solver.tryAddNamedAssertion(a3, "a3");
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_FALSE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

TEST_F(FullALIAUnsatCoreTest, Full_ALIA_Simple) {
    // a1 := select(arr1, x) != select(arr1,y)
    // a2 := select(arr1, x) == 0
    // a3 := x == y
    MainSolver solver = makeSolver();
    PTRef a1 = logic.mkNot(logic.mkEq(logic.mkSelect({arr1, x}), logic.mkSelect({arr1,y})));
    PTRef a2 = logic.mkEq(logic.mkSelect({arr1,x}), logic.getTerm_IntZero());
    PTRef a3 = logic.mkEq(x,y);
    solver.addAssertion(a1);
    solver.addAssertion(a2);
    solver.addAssertion(a3);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto core = solver.getUnsatCore();
    auto & coreTerms = core->getTerms();
    ASSERT_EQ(coreTerms.size(), 2);
    EXPECT_TRUE(isInCore(a1, coreTerms));
    EXPECT_FALSE(isInCore(a2, coreTerms));
    EXPECT_TRUE(isInCore(a3, coreTerms));
}

}
