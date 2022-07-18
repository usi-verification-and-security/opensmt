//
// Created by Martin Blicha on 06.11.20.
//

#include <gtest/gtest.h>
#include <ArithLogic.h>
#include <VerificationUtils.h>
#include <LIAInterpolator.h>
#include <MainSolver.h>

class LIAInterpolationTest : public ::testing::Test {
protected:
    LIAInterpolationTest(): logic{opensmt::Logic_t::QF_LIA} {}
    virtual void SetUp() {
        x = logic.mkIntVar("x");
        y = logic.mkIntVar("y");
        x1 = logic.mkIntVar("x1");
        x2 = logic.mkIntVar("x2");
        x3 = logic.mkIntVar("x3");
        x4 = logic.mkIntVar("x4");
    }
    ArithLogic logic;
    SMTConfig config;
    PTRef x, y, x1, x2, x3, x4;

    bool verifyInterpolant(PTRef A, PTRef B, PTRef itp) {
        return VerificationUtils(logic).verifyInterpolantInternal(A, B, itp);
    }
};

TEST_F(LIAInterpolationTest, test_InterpolationLRASat){
    /*
     * A:   x > 0
     *
     * B    x < 1
     */
    PTRef zero = logic.getTerm_IntZero();
    PTRef one = logic.getTerm_IntOne();
    PTRef leq1 = logic.mkGt(x, zero);
    PTRef leq2 = logic.mkLt(x, one);
    vec<PtAsgn> conflict {PtAsgn(logic.mkNot(leq1), l_False), PtAsgn(logic.mkNot(leq2), l_False)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, icolor_t::I_A}, {conflict[1].tr, icolor_t::I_B}};
    LIAInterpolator interpolator(logic, LAExplanations::getLIAExplanation(logic, conflict, {1,1}, labels));
    PTRef farkasItp = interpolator.getFarkasInterpolant();
    std::cout << logic.pp(farkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(leq1, leq2, farkasItp));
    PTRef dualFarkasItp = interpolator.getDualFarkasInterpolant();
    std::cout << logic.pp(dualFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(leq1, leq2, dualFarkasItp));
    PTRef halfFarkasItp = interpolator.getFlexibleInterpolant(FastRational(1,2));
    std::cout << logic.pp(halfFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(leq1, leq2, halfFarkasItp));
}

TEST_F(LIAInterpolationTest, test_DecompositionInLIA){
    /*
     * A:   x1 > -1
     *      x2 - x1 > -1
     *      -x3 - x1 > -1
     * B:
     *      x3 - x4 > 0
     *      -x4 - x2 >= 0
     *      x4 >= 0
     */
    PTRef zero = logic.getTerm_IntZero();
    PTRef minusOne = logic.getTerm_IntMinusOne();
    PTRef leq1 = logic.mkGt(x1, minusOne);
    PTRef leq2 = logic.mkGt(logic.mkMinus(x2,x1), minusOne);
    PTRef leq3 = logic.mkGt(logic.mkNeg(logic.mkPlus(x3,x1)), minusOne);

    PTRef leq4 = logic.mkGt(logic.mkMinus(x3,x4), zero);
    PTRef leq5 = logic.mkGeq(logic.mkNeg(logic.mkPlus(x4,x2)), zero);
    PTRef leq6 = logic.mkGeq(x4, zero);
    vec<PtAsgn> conflict {PtAsgn(logic.mkNot(leq1), l_False), PtAsgn(logic.mkNot(leq2), l_False),
                          PtAsgn(logic.mkNot(leq3), l_False),
                          PtAsgn(logic.mkNot(leq4), l_False), PtAsgn(leq5, l_True), PtAsgn(leq6, l_True)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, icolor_t::I_A}, {conflict[1].tr, icolor_t::I_A}, {conflict[2].tr, icolor_t::I_A},
                                      {conflict[3].tr, icolor_t::I_B}, {conflict[4].tr, icolor_t::I_B}, {conflict[5].tr, icolor_t::I_B}};
    LIAInterpolator interpolator(logic, LAExplanations::getLIAExplanation(logic, std::move(conflict), {2,1,1,1,1,2}, labels));
    PTRef decomposedFarkasItp = interpolator.getDecomposedInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3}), logic.mkAnd({leq4, leq5, leq6}), decomposedFarkasItp));
    std::cout << logic.pp(decomposedFarkasItp) << std::endl;
    ASSERT_TRUE(logic.isAnd(decomposedFarkasItp));
    PTRef dualDecomposedFarkasItp = interpolator.getDualDecomposedInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3}), logic.mkAnd({leq4, leq5, leq6}), dualDecomposedFarkasItp));
//    std::cout << logic.pp(dualDecomposedFarkasItp) << std::endl;
}

TEST_F(LIAInterpolationTest, test_Split_ALocal){
    /*
     * A:   3y - 2x >= 0
     *      2x - y >= 2
     * B:
     *      y <= 1
     */
    PTRef zero = logic.getTerm_IntZero();
    PTRef one = logic.getTerm_IntOne();
    PTRef two = logic.mkConst("2");
    PTRef three = logic.mkConst("3");
    PTRef leq1 = logic.mkGeq(logic.mkMinus(logic.mkTimes(three, y), logic.mkTimes(two, x)), zero);
    PTRef leq2 = logic.mkGeq(logic.mkMinus(logic.mkTimes(two, x), y), two);

    PTRef leq3 = logic.mkLeq(y, one);

    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "test");
    PTRef partA = logic.mkAnd(leq1, leq2);
    PTRef partB = leq3;
    solver.insertFormula(partA);
    solver.insertFormula(partB);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    opensmt::setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.pp(interpolants[0]) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, interpolants[0]));
}

TEST_F(LIAInterpolationTest, test_Split_BLocal){
    /*
     * B:   3y - 2x >= 0
     *      2x - y >= 2
     * A:
     *      y <= 1
     */
    PTRef zero = logic.getTerm_IntZero();
    PTRef one = logic.getTerm_IntOne();
    PTRef two = logic.mkConst("2");
    PTRef three = logic.mkConst("3");
    PTRef leq1 = logic.mkGeq(logic.mkMinus(logic.mkTimes(three, y), logic.mkTimes(two, x)), zero);
    PTRef leq2 = logic.mkGeq(logic.mkMinus(logic.mkTimes(two, x), y), two);

    PTRef leq3 = logic.mkLeq(y, one);

    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "test");
    PTRef partB = logic.mkAnd(leq1, leq2);
    PTRef partA = leq3;
    solver.insertFormula(partA);
    solver.insertFormula(partB);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    opensmt::setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.pp(interpolants[0]) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, interpolants[0]));
}

TEST_F(LIAInterpolationTest, test_Split_ABShared) {
    /*
     * A:   3y - 2x >= 0
     *
     * B:
     *      2x - y >= 2
     *      y <= 1
     */
    PTRef zero = logic.getTerm_IntZero();
    PTRef one = logic.getTerm_IntOne();
    PTRef two = logic.mkConst("2");
    PTRef three = logic.mkConst("3");
    PTRef leq1 = logic.mkGeq(logic.mkMinus(logic.mkTimes(three, y), logic.mkTimes(two, x)), zero);
    PTRef leq2 = logic.mkGeq(logic.mkMinus(logic.mkTimes(two, x), y), two);
    PTRef leq3 = logic.mkLeq(y, one);

    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "test");
    PTRef partA = leq1;
    PTRef partB = logic.mkAnd(leq2, leq3);
    solver.insertFormula(partA);
    solver.insertFormula(partB);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    opensmt::setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.pp(interpolants[0]) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, interpolants[0]));
    interpolants.clear();
    config.setBooleanInterpolationAlgorithm(itp_alg_pudlak);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.pp(interpolants[0]) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, interpolants[0]));
    interpolants.clear();
    config.setBooleanInterpolationAlgorithm(itp_alg_mcmillanp);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.pp(interpolants[0]) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, interpolants[0]));
    interpolants.clear();
}