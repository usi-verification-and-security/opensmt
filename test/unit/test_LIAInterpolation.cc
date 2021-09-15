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
    LIAInterpolationTest(): logic{ArithLogic::ArithType::LIA} {}
    virtual void SetUp() {
        x = logic.mkNumVar("x");
        y = logic.mkNumVar("y");
        x1 = logic.mkNumVar("x1");
        x2 = logic.mkNumVar("x2");
        x3 = logic.mkNumVar("x3");
        x4 = logic.mkNumVar("x4");
    }
    ArithLogic logic;
    SMTConfig config;
    PTRef x, y, x1, x2, x3, x4;

    bool verifyInterpolant(PTRef A, PTRef B, PTRef itp) {
        return VerificationUtils(config, logic).verifyInterpolantInternal(A, B, itp);
    }
};

TEST_F(LIAInterpolationTest, test_InterpolationLRASat){
    /*
     * A:   x > 0
     *
     * B    x < 1
     */
    PTRef zero = logic.getTerm_NumZero();
    PTRef one = logic.getTerm_NumOne();
    PTRef leq1 = logic.mkNumGt(x, zero);
    PTRef leq2 = logic.mkNumLt(x, one);
    vec<PtAsgn> conflict {PtAsgn(logic.mkNot(leq1), l_False), PtAsgn(logic.mkNot(leq2), l_False)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, I_A}, {conflict[1].tr, I_B}};
    LIAInterpolator interpolator(logic, LAExplanations::getLIAExplanation(logic, conflict, {1,1}, labels));
    PTRef farkasItp = interpolator.getFarkasInterpolant();
    std::cout << logic.printTerm(farkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(leq1, leq2, farkasItp));
    PTRef dualFarkasItp = interpolator.getDualFarkasInterpolant();
    std::cout << logic.printTerm(dualFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(leq1, leq2, dualFarkasItp));
    PTRef halfFarkasItp = interpolator.getFlexibleInterpolant(FastRational(1,2));
    std::cout << logic.printTerm(halfFarkasItp) << std::endl;
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
    PTRef zero = logic.getTerm_NumZero();
    PTRef minusOne = logic.getTerm_NumMinusOne();
    PTRef leq1 = logic.mkIntGt(x1, minusOne);
    PTRef leq2 = logic.mkIntGt(logic.mkIntMinus(x2,x1), minusOne);
    PTRef leq3 = logic.mkIntGt(logic.mkIntNeg(logic.mkIntPlus(x3,x1)), minusOne);

    PTRef leq4 = logic.mkIntGt(logic.mkIntMinus(x3,x4), zero);
    PTRef leq5 = logic.mkIntGeq(logic.mkIntNeg(logic.mkIntPlus({x4,x2})), zero);
    PTRef leq6 = logic.mkIntGeq(x4, zero);
    vec<PtAsgn> conflict {PtAsgn(logic.mkNot(leq1), l_False), PtAsgn(logic.mkNot(leq2), l_False),
                          PtAsgn(logic.mkNot(leq3), l_False),
                          PtAsgn(logic.mkNot(leq4), l_False), PtAsgn(leq5, l_True), PtAsgn(leq6, l_True)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, I_A}, {conflict[1].tr, I_A}, {conflict[2].tr, I_A},
                                      {conflict[3].tr, I_B}, {conflict[4].tr, I_B}, {conflict[5].tr, I_B}};
    LIAInterpolator interpolator(logic, LAExplanations::getLIAExplanation(logic, std::move(conflict), {2,1,1,1,1,2}, labels));
    PTRef decomposedFarkasItp = interpolator.getDecomposedInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3}), logic.mkAnd({leq4, leq5, leq6}), decomposedFarkasItp));
    std::cout << logic.printTerm(decomposedFarkasItp) << std::endl;
    ASSERT_TRUE(logic.isAnd(decomposedFarkasItp));
    PTRef dualDecomposedFarkasItp = interpolator.getDualDecomposedInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3}), logic.mkAnd({leq4, leq5, leq6}), dualDecomposedFarkasItp));
//    std::cout << logic.printTerm(dualDecomposedFarkasItp) << std::endl;
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
    PTRef leq1 = logic.mkIntGeq(logic.mkIntMinus(logic.mkIntTimes(three, y), logic.mkIntTimes(two, x)), zero);
    PTRef leq2 = logic.mkIntGeq(logic.mkIntMinus(logic.mkIntTimes(two, x), y), two);

    PTRef leq3 = logic.mkIntLeq(y, one);

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
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.printTerm(interpolants[0]) << std::endl;
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
    PTRef leq1 = logic.mkIntGeq(logic.mkIntMinus(logic.mkIntTimes(three, y), logic.mkIntTimes(two, x)), zero);
    PTRef leq2 = logic.mkIntGeq(logic.mkIntMinus(logic.mkIntTimes(two, x), y), two);

    PTRef leq3 = logic.mkNumLeq(y, one);

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
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.printTerm(interpolants[0]) << std::endl;
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
    PTRef leq1 = logic.mkIntGeq(logic.mkIntMinus(logic.mkIntTimes(three, y), logic.mkIntTimes(two, x)), zero);
    PTRef leq2 = logic.mkIntGeq(logic.mkIntMinus(logic.mkIntTimes(two, x), y), two);
    PTRef leq3 = logic.mkIntLeq(y, one);

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
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.printTerm(interpolants[0]) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, interpolants[0]));
    interpolants.clear();
    config.setBooleanInterpolationAlgorithm(itp_alg_pudlak);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.printTerm(interpolants[0]) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, interpolants[0]));
    interpolants.clear();
    config.setBooleanInterpolationAlgorithm(itp_alg_mcmillanp);
    itpCtx->getSingleInterpolant(interpolants, mask);
    std::cout << logic.printTerm(interpolants[0]) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, interpolants[0]));
    interpolants.clear();
}