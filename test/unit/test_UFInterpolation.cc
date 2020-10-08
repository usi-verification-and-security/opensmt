//
// Created by Martin Blicha on 19.09.20.
//

#include <gtest/gtest.h>
#include <Logic.h>
#include <MainSolver.h>
#include "VerificationUtils.h"

class UFInterpolationTest : public ::testing::Test {
protected:
    UFInterpolationTest(): logic{} {}
    virtual void SetUp() {
        ufsort = logic.declareSort("U", nullptr);
        x = logic.mkVar(ufsort, "x");
        y = logic.mkVar(ufsort, "y");
        x1 = logic.mkVar(ufsort, "x1");
        x2 = logic.mkVar(ufsort, "x2");
        x3 = logic.mkVar(ufsort, "x3");
        x4 = logic.mkVar(ufsort, "x4");
        y1 = logic.mkVar(ufsort, "y1");
        y2 = logic.mkVar(ufsort, "y2");
        z1 = logic.mkVar(ufsort, "z1");
        z2 = logic.mkVar(ufsort, "z2");
        z3 = logic.mkVar(ufsort, "z3");
        z4 = logic.mkVar(ufsort, "z4");
        z5 = logic.mkVar(ufsort, "z5");
        z6 = logic.mkVar(ufsort, "z6");
        z7 = logic.mkVar(ufsort, "z7");
        z8 = logic.mkVar(ufsort, "z8");
        char* msg;
        f = logic.declareFun("f", ufsort, {ufsort}, &msg, false);
        g = logic.declareFun("g", ufsort, {ufsort, ufsort}, &msg, false);
        p = logic.declareFun("p", logic.getSort_bool(), {ufsort}, &msg, false);
    }
    Logic logic;
    SMTConfig config;
    SRef ufsort;
    PTRef x, y, x1, x2, x3, x4, y1, y2, z1, z2, z3, z4, z5, z6, z7, z8;
    SymRef f, g, p;

    bool verifyInterpolant(PTRef itp, PartitionManager & pManager, ipartitions_t const & Amask) {
        return VerificationUtils(config, logic).verifyInterpolantInternal(pManager.getPartition(Amask, PartitionManager::part::A), pManager.getPartition(Amask, PartitionManager::part::B), itp);
    }

};

TEST_F(UFInterpolationTest, test_SimpleTransitivity){
    /*
     * Simple conflict x=y, y=z, not(x=z)
     */
    PTRef eq1 = logic.mkEq(x,y);
    PTRef eq2 = logic.mkEq(y,z1);
    PTRef eq3 = logic.mkEq(z1,x);
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(eq1);
    solver.insertFormula(eq2);
    solver.insertFormula(logic.mkNot(eq3));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
    interpolants.clear();
    setbit(mask, 1);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_SimpleTransitivityReversed){
    /*
     * Same as SimpleTransitivy but the disequality is always in A instead of B
     */
    PTRef eq1 = logic.mkEq(x,y);
    PTRef eq2 = logic.mkEq(y,z1);
    PTRef eq3 = logic.mkEq(z1,x);
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(logic.mkNot(eq3));
    solver.insertFormula(eq2);
    solver.insertFormula(eq1);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
    interpolants.clear();
    setbit(mask, 1);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_SimpleCongruence){
    /*
     * Simple conflict using congruence: x=y, f(x) != f(y)
     */
    PTRef eq1 = logic.mkEq(x,y);
    PTRef eq2 = logic.mkEq(logic.mkUninterpFun(f, {x}), logic.mkUninterpFun(f, {y}));
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(eq1);
    solver.insertFormula(logic.mkNot(eq2));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_SimpleCongruenceReversed){
    /*
     * Same as SimpleCongruence, but the disequality is in A, not B
     */
    PTRef eq1 = logic.mkEq(x,y);
    PTRef eq2 = logic.mkEq(logic.mkUninterpFun(f, {x}), logic.mkUninterpFun(f, {y}));
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(logic.mkNot(eq2));
    solver.insertFormula(eq1);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_NotImmediatelyColorableCGraph){
    /*
     * A = {x=z1, g(x,z2)=z3}; B = {y=z2, not(g(z1,y)=z3)}
     */
    PTRef eqA1 = logic.mkEq(x,z1);
    PTRef eqA2 = logic.mkEq(logic.mkUninterpFun(g, {x,z2}),z3);
    PTRef eqB1 = logic.mkEq(y,z2);
    PTRef eqB2 = logic.mkEq(logic.mkUninterpFun(g, {z1,y}),z3);
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(logic.mkAnd(eqA1, eqA2));
    solver.insertFormula(logic.mkAnd(eqB1, logic.mkNot(eqB2)));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
    // change the interpolation algorithm
    config.setEUFInterpolationAlgorithm(itp_euf_alg_weak);
    interpolants.clear();
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_NotImmediatelyColorableCGraphReversed){
    /*
     * Same as NotImmediatelyColorableCGraph, but reversed A and B
     * B = {x=z1, g(x,z2)=z3}; A = {y=z2, not(g(z1,y)=z3)}
     */
    PTRef eqB1 = logic.mkEq(x,z1);
    PTRef eqB2 = logic.mkEq(logic.mkUninterpFun(g, {x,z2}),z3);
    PTRef eqA1 = logic.mkEq(y,z2);
    PTRef eqA2 = logic.mkEq(logic.mkUninterpFun(g, {z1,y}),z3);
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(logic.mkAnd(eqA1, logic.mkNot(eqA2)));
    solver.insertFormula(logic.mkAnd(eqB1, eqB2));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
    // change the interpolation algorithm
    config.setEUFInterpolationAlgorithm(itp_euf_alg_weak);
    interpolants.clear();
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_JustificationRequired){
    /*
     * A = {x1=z1, z2=x2, z3=f(x1), f(x2)=z4, x3=z5, z6=x4, z7=f(x3), f(x4)=z8}
     * B = {z1=z2, z5=f(z3), f(z4)=z6, y1=z7, z8=y2, not(y1=y2)}
     */
    PTRef eqA1 = logic.mkEq(x1,z1);
    PTRef eqA2 = logic.mkEq(z2,x2);
    PTRef eqA3 = logic.mkEq(z3,logic.mkUninterpFun(f, {x1}));
    PTRef eqA4 = logic.mkEq(logic.mkUninterpFun(f, {x2}), z4);
    PTRef eqA5 = logic.mkEq(x3,z5);
    PTRef eqA6 = logic.mkEq(z6,x4);
    PTRef eqA7 = logic.mkEq(z7,logic.mkUninterpFun(f, {x3}));
    PTRef eqA8 = logic.mkEq(logic.mkUninterpFun(f, {x4}), z8);
    PTRef eqB1 = logic.mkEq(z1,z2);
    PTRef eqB2 = logic.mkEq(z5,logic.mkUninterpFun(f, {z3}));
    PTRef eqB3 = logic.mkEq(logic.mkUninterpFun(f, {z4}), z6);
    PTRef eqB4 = logic.mkEq(y1,z7);
    PTRef eqB5 = logic.mkEq(z8,y2);
    PTRef eqB6 = logic.mkEq(y1,y2);
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(logic.mkAnd({eqA1, eqA2, eqA3, eqA4, eqA5, eqA6, eqA7, eqA8}));
    solver.insertFormula(logic.mkAnd({eqB1, eqB2, eqB3, eqB4, eqB5, logic.mkNot(eqB6)}));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
    // change the interpolation algorithm
    config.setEUFInterpolationAlgorithm(itp_euf_alg_weak);
    interpolants.clear();
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_JustificationRequiredReversed){
    /*
     * Same as JustificationRequired, but A and B switched
     * B = {x1=z1, z2=x2, z3=f(x1), f(x2)=z4, x3=z5, z6=x4, z7=f(x3), f(x4)=z8}
     * A = {z1=z2, z5=f(z3), f(z4)=z6, y1=z7, z8=y2, not(y1=y2)}
     */
    PTRef eqB1 = logic.mkEq(x1,z1);
    PTRef eqB2 = logic.mkEq(z2,x2);
    PTRef eqB3 = logic.mkEq(z3,logic.mkUninterpFun(f, {x1}));
    PTRef eqB4 = logic.mkEq(logic.mkUninterpFun(f, {x2}), z4);
    PTRef eqB5 = logic.mkEq(x3,z5);
    PTRef eqB6 = logic.mkEq(z6,x4);
    PTRef eqB7 = logic.mkEq(z7,logic.mkUninterpFun(f, {x3}));
    PTRef eqB8 = logic.mkEq(logic.mkUninterpFun(f, {x4}), z8);
    PTRef eqA1 = logic.mkEq(z1,z2);
    PTRef eqA2 = logic.mkEq(z5,logic.mkUninterpFun(f, {z3}));
    PTRef eqA3 = logic.mkEq(logic.mkUninterpFun(f, {z4}), z6);
    PTRef eqA4 = logic.mkEq(y1,z7);
    PTRef eqA5 = logic.mkEq(z8,y2);
    PTRef eqA6 = logic.mkEq(y1,y2);
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(logic.mkAnd({eqA1, eqA2, eqA3, eqA4, eqA5, logic.mkNot(eqA6)}));
    solver.insertFormula(logic.mkAnd({eqB1, eqB2, eqB3, eqB4, eqB5, eqB6, eqB7,eqB8}));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
    // change the interpolation algorithm
    config.setEUFInterpolationAlgorithm(itp_euf_alg_weak);
    interpolants.clear();
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_SimpleUninterpretedPredicate){
    /*
     * Simple conflict using congruence: x=y, P(x), not(P(y))
     */
    PTRef eq = logic.mkEq(x,y);
    PTRef px = logic.mkUninterpFun(p, {x});
    PTRef py = logic.mkUninterpFun(p, {y});
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(px);
    solver.insertFormula(eq);
    solver.insertFormula(logic.mkNot(py));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_ConstantsConflict){
    /*
     * Simple conflict using uninterpreted constants (implicitly different): c=x, x=d
     */
    PTRef c = logic.mkConst(ufsort, "c");
    PTRef d = logic.mkConst(ufsort, "d");
    PTRef eqA = logic.mkEq(c,x);
    PTRef eqB = logic.mkEq(x,d);
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(eqA);
    solver.insertFormula(eqB);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_TwoLevelJustification){
    /*
     * B = {z1=g(y1,z3}, g(y1,z4)=z2
     * A = {x1=f(z1), x2=f(z2), z3=z4}
     * not(x1=x2) in A
     */
    PTRef eqB1 = logic.mkEq(z1,logic.mkUninterpFun(g, {y1,z3}));
    PTRef eqB2 = logic.mkEq(logic.mkUninterpFun(g, {y1, z4}), z2);
    PTRef eqA1 = logic.mkEq(x1,logic.mkUninterpFun(f, {z1}));
    PTRef eqA2 = logic.mkEq(logic.mkUninterpFun(f, {z2}), x2);
    PTRef eqA3 = logic.mkEq(z3,z4);
    PTRef dis = logic.mkNot(logic.mkEq(x1, x2));
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(logic.mkAnd({eqA1, eqA2, eqA3, dis}));
    solver.insertFormula(logic.mkAnd({eqB1, eqB2}));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
    // change the interpolation algorithm
    config.setEUFInterpolationAlgorithm(itp_euf_alg_weak);
    interpolants.clear();
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}

TEST_F(UFInterpolationTest, test_TwoLevelJustificationDiseqInB){
    /*
     * B = {z1=g(y1,z3}, g(y1,z4)=z2
     * A = {x1=f(z1), x2=f(z2), z3=z4}
     * not(x1=x2) in B
     */
    PTRef eqB1 = logic.mkEq(z1,logic.mkUninterpFun(g, {y1,z3}));
    PTRef eqB2 = logic.mkEq(logic.mkUninterpFun(g, {y1, z4}), z2);
    PTRef eqA1 = logic.mkEq(x1,logic.mkUninterpFun(f, {z1}));
    PTRef eqA2 = logic.mkEq(logic.mkUninterpFun(f, {z2}), x2);
    PTRef eqA3 = logic.mkEq(z3,z4);
    PTRef dis = logic.mkNot(logic.mkEq(x1, x2));
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "ufinterpolator");
    solver.insertFormula(logic.mkAnd({eqA1, eqA2, eqA3}));
    solver.insertFormula(logic.mkAnd({eqB1, eqB2, dis}));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
    // change the interpolation algorithm
    config.setEUFInterpolationAlgorithm(itp_euf_alg_weak);
    interpolants.clear();
    itpCtx->getSingleInterpolant(interpolants, mask);
    EXPECT_TRUE(verifyInterpolant(interpolants[0], solver.getPartitionManager(), mask));
}


