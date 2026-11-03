//
// Created by Martin Blicha on 06.11.20.
//

#include <gtest/gtest.h>
#include <logics/ArithLogic.h>
#include <common/VerificationUtils.h>
#include <tsolvers/lasolver/LIAInterpolator.h>
#include <tsolvers/lasolver/LASolver.h>
#include <api/MainSolver.h>

#include <unordered_map>

namespace opensmt {

using ItpColorMap = LIAInterpolator::ItpColorMap;

class LIAInterpolationTest : public ::testing::Test {
protected:
    LIAInterpolationTest(): logic{Logic_t::QF_LIA} {}
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

    // Solves A /\ B and returns the interpolant for partition A, or PTRef_Undef if A /\ B is not unsat
    PTRef computeInterpolant(PTRef partA, PTRef partB) {
        const char* msg = "ok";
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        MainSolver solver(logic, config, "test");
        solver.insertFormula(partA);
        solver.insertFormula(partB);
        if (solver.check() != s_False) { return PTRef_Undef; }
        auto itpCtx = solver.getInterpolationContext();
        vec<PTRef> interpolants;
        ipartitions_t mask;
        setbit(mask, 0);
        itpCtx->getSingleInterpolant(interpolants, mask);
        return interpolants[0];
    }

    void expectNoAuxiliaryVars(PTRef itp) {
        std::string itpStr = logic.pp(itp);
        EXPECT_EQ(itpStr.find(".mod"), std::string::npos) << "Interpolant leaks auxiliary mod variable: " << itpStr;
        EXPECT_EQ(itpStr.find(".div"), std::string::npos) << "Interpolant leaks auxiliary div variable: " << itpStr;
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
    ItpColorMap labels {{conflict[0].tr, icolor_t::I_A}, {conflict[1].tr, icolor_t::I_B}};
    LIAInterpolator interpolator(logic, LAExplanations::getLIAExplanation(logic, conflict, {1,1}, labels));
    PTRef farkasItp = interpolator.getFarkasInterpolant();
    std::cout << logic.pp(farkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(leq1, leq2, farkasItp));
    PTRef dualFarkasItp = interpolator.getDualFarkasInterpolant();
    std::cout << logic.pp(dualFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(leq1, leq2, dualFarkasItp));
    // not implemented for integers
    // PTRef halfFarkasItp = interpolator.getFlexibleInterpolant(Number(1,2));
    // std::cout << logic.pp(halfFarkasItp) << std::endl;
    // EXPECT_TRUE(verifyInterpolant(leq1, leq2, halfFarkasItp));
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
    ItpColorMap labels {{conflict[0].tr, icolor_t::I_A}, {conflict[1].tr, icolor_t::I_A}, {conflict[2].tr, icolor_t::I_A},
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
    setbit(mask, 0);
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
    setbit(mask, 0);
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
    setbit(mask, 0);
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

TEST_F(LIAInterpolationTest, test_CorrectHandlingOfFractionalCoefficientsInExplanation){
    /*
     * A:   x <= 10
     *      3x - y >= 0
     *
     * B    y >= 50
     */
    PTRef leq1 = logic.mkLeq(x, logic.mkIntConst(10));
    PTRef leq2 = logic.mkGeq(logic.mkMinus(logic.mkTimes(logic.mkIntConst(3), x), y), logic.mkIntConst(0));
    PTRef leq3 = logic.mkGeq(y, logic.mkIntConst(50));


    vec<PtAsgn> conflict {PtAsgn(leq1, l_True), PtAsgn(leq2, l_True), PtAsgn(leq3, l_True)};
    ItpColorMap labels {{conflict[0].tr, icolor_t::I_A}, {conflict[1].tr, icolor_t::I_A}, {conflict[2].tr, icolor_t::I_B}};
    LIAInterpolator interpolator(logic, LAExplanations::getLIAExplanation(logic, conflict, {1, FastRational{1,3}, 1}, labels));
    PTRef farkasItp = interpolator.getFarkasInterpolant();
    std::cout << logic.pp(farkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), leq3, farkasItp));
}

TEST_F(LIAInterpolationTest, test_CorrectHandlingOfMods){
    /*
     * A:  mod(x,10) < 5
     *
     * B:  mod(x,10) > 6
     */
    PTRef partA = logic.mkLeq(logic.mkMod(x,  logic.mkIntConst(10)), logic.mkIntConst(4));
    PTRef partB = logic.mkLeq(logic.mkIntConst(7), logic.mkMod(x,  logic.mkIntConst(10)));

    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "test");
    solver.insertFormula(partA);
    solver.insertFormula(partB);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    PTRef farkasItp = interpolants[0];
    EXPECT_TRUE(verifyInterpolant(partA, partB, farkasItp));
}

// Found through Golem's TPA engine, whose interpolation queries contain the same mod term in both partitions:
// a negated divisibility constraint in A and the constraint itself in B.
TEST_F(LIAInterpolationTest, test_NegatedDivisibilityConstraint){
    /*
     * A:  (not (= 0 (mod x 25)))
     *
     * B:  (= 0 (mod x 25))
     */
    PTRef divisible = logic.mkEq(logic.getTerm_IntZero(), logic.mkMod(x, logic.mkIntConst(25)));
    PTRef partA = logic.mkNot(divisible);
    PTRef partB = divisible;

    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "test");
    solver.insertFormula(partA);
    solver.insertFormula(partB);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    PTRef itp = interpolants[0];

    std::string itpStr = logic.pp(itp);
    EXPECT_EQ(itpStr.find(".mod"), std::string::npos) << "Interpolant leaks auxiliary mod variable: " << itpStr;
    EXPECT_EQ(itpStr.find(".div"), std::string::npos) << "Interpolant leaks auxiliary div variable: " << itpStr;
    EXPECT_TRUE(verifyInterpolant(partA, partB, itp));
}

TEST_F(LIAInterpolationTest, test_NegatedDivisibilityConstraint_SimplifiedInterpolant){
    /*
     * Same query, with the interpolant simplification Golem uses (:simplify-interpolants 4)
     *
     * A:  (not (= 0 (mod x 25)))
     *
     * B:  (= 0 (mod x 25))
     */
    PTRef divisible = logic.mkEq(logic.getTerm_IntZero(), logic.mkMod(x, logic.mkIntConst(25)));
    PTRef partA = logic.mkNot(divisible);
    PTRef partB = divisible;

    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    config.setOption(SMTConfig::o_simplify_inter, SMTOption(4), msg);
    MainSolver solver(logic, config, "test");
    solver.insertFormula(partA);
    solver.insertFormula(partB);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    PTRef itp = interpolants[0];

    std::string itpStr = logic.pp(itp);
    EXPECT_EQ(itpStr.find(".mod"), std::string::npos) << "Interpolant leaks auxiliary mod variable: " << itpStr;
    EXPECT_EQ(itpStr.find(".div"), std::string::npos) << "Interpolant leaks auxiliary div variable: " << itpStr;
    EXPECT_TRUE(verifyInterpolant(partA, partB, itp));
}

TEST_F(LIAInterpolationTest, test_ModBoundAgainstDivisibilityConstraint){
    /*
     * The same contradiction, with A written as a bound
     *
     * A:  (<= 1 (mod x 25))
     *
     * B:  (= 0 (mod x 25))
     */
    PTRef mod = logic.mkMod(x, logic.mkIntConst(25));
    PTRef partA = logic.mkLeq(logic.getTerm_IntOne(), mod);
    PTRef partB = logic.mkEq(logic.getTerm_IntZero(), mod);

    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "test");
    solver.insertFormula(partA);
    solver.insertFormula(partB);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    PTRef itp = interpolants[0];

    EXPECT_TRUE(verifyInterpolant(partA, partB, itp));
}

TEST_F(LIAInterpolationTest, test_NestedDivModBoundAgainstDivisibilityConstraint){
    /*
     * The same contradiction, over a mod of a div: the auxiliary variable for the outer mod is defined in terms
     * of the auxiliary variable for the inner div, so both must be translated back
     *
     * A:  (<= 1 (mod (div x 3) 5))
     *
     * B:  (= 0 (mod (div x 3) 5))
     */
    PTRef mod = logic.mkMod(logic.mkIntDiv(x, logic.mkIntConst(3)), logic.mkIntConst(5));
    PTRef partA = logic.mkLeq(logic.getTerm_IntOne(), mod);
    PTRef partB = logic.mkEq(logic.getTerm_IntZero(), mod);

    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "test");
    solver.insertFormula(partA);
    solver.insertFormula(partB);
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
    auto itpCtx = solver.getInterpolationContext();
    vec<PTRef> interpolants;
    ipartitions_t mask;
    setbit(mask, 0);
    itpCtx->getSingleInterpolant(interpolants, mask);
    PTRef itp = interpolants[0];

    EXPECT_TRUE(verifyInterpolant(partA, partB, itp));
}

TEST_F(LIAInterpolationTest, test_Split_DivisibilityByFactors){
    /*
     * A:  mod(x,2) = 0 and mod(x,3) = 0
     *
     * B:  not mod(x,6) = 0
     */
    PTRef zero = logic.getTerm_IntZero();
    PTRef partA = logic.mkAnd(logic.mkEq(logic.mkMod(x, logic.mkIntConst(2)), zero),
                              logic.mkEq(logic.mkMod(x, logic.mkIntConst(3)), zero));
    PTRef partB = logic.mkNot(logic.mkEq(logic.mkMod(x, logic.mkIntConst(6)), zero));

    PTRef itp = computeInterpolant(partA, partB);
    ASSERT_NE(itp, PTRef_Undef);
    std::cout << logic.pp(itp) << std::endl;
    expectNoAuxiliaryVars(itp);
    EXPECT_TRUE(verifyInterpolant(partA, partB, itp));
}

TEST_F(LIAInterpolationTest, test_Split_EvenAndOddBetweenBounds){
    /*
     * A:  t <= 2a <= r
     *
     * B:  r <= 2b + 1 <= t
     */
    PTRef t = logic.mkIntVar("t");
    PTRef a = logic.mkIntVar("a");
    PTRef b = logic.mkIntVar("b");
    PTRef r = logic.mkIntVar("r");
    PTRef two = logic.mkIntConst(2);
    PTRef twoA = logic.mkTimes(two, a);
    PTRef twoBPlusOne = logic.mkPlus(logic.mkTimes(two, b), logic.getTerm_IntOne());
    PTRef partA = logic.mkAnd(logic.mkLeq(t, twoA), logic.mkLeq(twoA, r));
    PTRef partB = logic.mkAnd(logic.mkLeq(r, twoBPlusOne), logic.mkLeq(twoBPlusOne, t));

    PTRef itp = computeInterpolant(partA, partB);
    ASSERT_NE(itp, PTRef_Undef);
    std::cout << logic.pp(itp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, itp));
}

TEST_F(LIAInterpolationTest, test_Split_DisjunctiveTransitionQuery){
    /*
     * Transition-system style query over two unrollings of variables x2, x3
     *
     * A:  (x3_0 - x3_1 = 1 and x2_0 = x2_1 and x3_1 >= 0)
     *     or (x2_1 = x3_1 and x2_0 - x3_1 = 1 and x3_0 <= 0 and x3_1 >= 1)
     *
     * B:  (disjunction of bad states over x2_1, x3_1) and not (disjunction of initial states over x2_0, x3_0)
     */
    PTRef x20 = logic.mkIntVar("x#2##0");
    PTRef x30 = logic.mkIntVar("x#3##0");
    PTRef x21 = logic.mkIntVar("x#2##1");
    PTRef x31 = logic.mkIntVar("x#3##1");
    auto c = [this](int n) { return logic.mkIntConst(n); };
    auto neg = [this](PTRef v) { return logic.mkNeg(v); };
    auto minus = [this](PTRef v, PTRef w) { return logic.mkMinus(v, w); };
    auto leq = [this](PTRef v, PTRef w) { return logic.mkLeq(v, w); };
    auto eq = [this](PTRef v, PTRef w) { return logic.mkEq(v, w); };

    PTRef partA = logic.mkOr(
        logic.mkAnd({eq(c(1), minus(x30, x31)), eq(c(0), minus(x20, x21)), leq(c(0), x31)}),
        logic.mkAnd({eq(c(0), minus(x21, x31)), eq(c(1), minus(x20, x31)), leq(c(0), neg(x30)), leq(c(1), x31)}));

    PTRef x31Positive = logic.mkNot(leq(c(0), neg(x31)));
    PTRef bad = logic.mkOr({
        logic.mkAnd({leq(c(0), x31), x31Positive, leq(c(2), minus(x21, x31))}),
        logic.mkAnd({leq(c(1), x21), x31Positive, leq(c(-1), neg(x21)), leq(c(-2), minus(x21, x31)), leq(c(2), minus(x31, x21))}),
        logic.mkAnd({leq(c(1), x21), x31Positive, leq(c(-1), neg(x21)), leq(c(2), minus(x31, x21))}),
        logic.mkAnd({leq(c(1), x21), x31Positive, leq(c(-2), minus(x21, x31)), leq(c(2), minus(x31, x21))}),
        logic.mkAnd({leq(c(1), x21), x31Positive, leq(c(2), minus(x31, x21))})});
    PTRef init = logic.mkOr({
        logic.mkAnd({leq(c(2), x30), leq(c(1), minus(x20, x30))}),
        logic.mkAnd({leq(c(1), x20), leq(c(-1), neg(x20)), leq(c(2), x30), leq(c(-3), minus(x20, x30)), leq(c(3), minus(x30, x20))}),
        logic.mkAnd({leq(c(1), x20), leq(c(2), x30), leq(c(3), minus(x30, x20))})});
    PTRef partB = logic.mkAnd(bad, logic.mkNot(init));

    PTRef itp = computeInterpolant(partA, partB);
    ASSERT_NE(itp, PTRef_Undef);
    std::cout << logic.pp(itp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(partA, partB, itp));
}

TEST_F(LIAInterpolationTest, test_SharedTermInFirstAndThirdPartition){
    /*
     * Partition 0:  y > 0
     * Partition 1:  true
     * Partition 2:  y <= 0
     *
     * A = partition 0, B = partitions 1 and 2. The partition mask of y is 0b101, which must not be confused with
     * a term mixing A-local and B-local variables.
     */
    PTRef zero = logic.getTerm_IntZero();
    PTRef p0 = logic.mkGt(y, zero);
    PTRef p1 = logic.getTerm_true();
    PTRef p2 = logic.mkLeq(y, zero);

    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    MainSolver solver(logic, config, "test");
    solver.insertFormula(p0);
    solver.insertFormula(p1);
    solver.insertFormula(p2);
    ASSERT_EQ(solver.check(), s_False);
    auto itpCtx = solver.getInterpolationContext();
    for (int aPartitions : {1, 2}) { // A = {0} and A = {0, 1}
        vec<PTRef> interpolants;
        ipartitions_t mask;
        for (int i = 0; i < aPartitions; ++i) { setbit(mask, i); }
        itpCtx->getSingleInterpolant(interpolants, mask);
        std::cout << logic.pp(interpolants[0]) << std::endl;
        PTRef partA = aPartitions == 1 ? p0 : logic.mkAnd(p0, p1);
        PTRef partB = aPartitions == 1 ? logic.mkAnd(p1, p2) : p2;
        EXPECT_TRUE(verifyInterpolant(partA, partB, interpolants[0]));
    }
}

namespace {
// Colors terms from an explicit map, standing in for the partition-based GlobalTermColorInfo that
// LASolver hands to the interpolator. Needed for mixed literals: their variables are not in the labels.
class FixedTermColorInfo : public TermColorInfo {
public:
    explicit FixedTermColorInfo(std::unordered_map<PTRef, icolor_t, PTRefHash> colors) : colors(std::move(colors)) {}
    icolor_t getColorFor(PTRef term) override { return colors.at(term); }

private:
    std::unordered_map<PTRef, icolor_t, PTRefHash> colors;
};
} // namespace

TEST_F(LIAInterpolationTest, test_SplitMixedLiteral_LeafInterpolants) {
    /*
     * Conflict:  0 <= x + y  (mixed: x is A-local, y is B-local),   x <= -1  (A),   y <= 0  (B)
     *
     * splitMixedLiteral splits the mixed literal with the fresh shared variable m = .mixed_<id> into
     *   0 <= x - m  (A half)   and   0 <= y + m  (B half)
     * A side:  (x - m) + (-1 - x) = -1 - m,  i.e. the partial interpolant  m <= -1
     * B side:  (y + m) + (-y)     = m,       i.e. 0 <= m, returned negated: not (0 <= m)
     */
    PTRef zero = logic.getTerm_IntZero();
    PTRef mixed = logic.mkLeq(zero, logic.mkPlus(x, y));
    PTRef aLit = logic.mkLeq(x, logic.mkIntConst(-1));
    PTRef bLit = logic.mkLeq(y, zero);
    vec<PtAsgn> conflict{PtAsgn(mixed, l_True), PtAsgn(aLit, l_True), PtAsgn(bLit, l_True)};
    ItpColorMap labels{{mixed, icolor_t::I_MIXED}, {aLit, icolor_t::I_A}, {bLit, icolor_t::I_B}};
    LIAInterpolator interpolator(
        logic, LAExplanations::getLIAExplanation(logic, conflict, {1, 1, 1}, labels),
        std::make_unique<FixedTermColorInfo>(std::unordered_map<PTRef, icolor_t, PTRefHash>{
            {x, icolor_t::I_A}, {y, icolor_t::I_B}}));
    PTRef m = logic.mkIntVar((".mixed_" + std::to_string(mixed.x)).c_str());
    PTRef expected = logic.mkLeq(m, logic.mkIntConst(-1));
    VerificationUtils verifier(logic);

    PTRef itpA = interpolator.getFarkasInterpolant();
    std::cout << logic.pp(itpA) << std::endl;
    EXPECT_TRUE(verifier.impliesInternal(itpA, expected));
    EXPECT_TRUE(verifier.impliesInternal(expected, itpA));
    ASSERT_EQ(interpolator.getMixedLAInfo().size(), 1u);
    {
        auto const & info = interpolator.getMixedLAInfo()[0];
        EXPECT_EQ(info.auxVar, m);
        EXPECT_EQ(info.coeff, Real(1)); // m <= -1 is  m + 1 <| 0
        EXPECT_EQ(info.k, Real(-1));    // leaf value of k
        EXPECT_FALSE(info.strict);
    }

    PTRef itpB = interpolator.getDualFarkasInterpolant();
    std::cout << logic.pp(itpB) << std::endl;
    // not (0 <= m) is m < 0, which over the integers is again m <= -1
    EXPECT_TRUE(verifier.impliesInternal(itpB, expected));
    EXPECT_TRUE(verifier.impliesInternal(expected, itpB));
    ASSERT_EQ(interpolator.getMixedLAInfo().size(), 1u); // cleared and recomputed for the dual
    {
        auto const & info = interpolator.getMixedLAInfo()[0];
        EXPECT_EQ(info.auxVar, m);
        EXPECT_EQ(info.coeff, Real(-1)); // 0 <= m is  -m <| 0
        EXPECT_EQ(info.k, Real(-1));
        EXPECT_FALSE(info.strict);
    }
}

TEST_F(LIAInterpolationTest, test_ResolveMixed_UnitCoefficients) {
    /*
     * Pivot p := y <= x with fresh shared variable m = .mixed_<p>
     *
     * left:  m <= x1     right:  x2 <= m
     *
     * Eliminating m by summing the two sides gives  x2 <= x1
     */
    LASolver solver(config, logic);
    PTRef pivot = logic.mkLeq(y, x);
    PTRef m = logic.mkIntVar((".mixed_" + std::to_string(pivot.x)).c_str());
    PTRef left = logic.mkLeq(m, x1);
    PTRef right = logic.mkLeq(x2, m);
    PTRef expected = logic.mkLeq(x2, x1);
    VerificationUtils verifier(logic);

    PTRef res = solver.resolveMixed(pivot, left, right);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_TRUE(verifier.impliesInternal(res, expected));
    EXPECT_TRUE(verifier.impliesInternal(expected, res));

    // A side that does not mention the pivot's variable is returned unchanged
    EXPECT_EQ(solver.resolveMixed(pivot, left, expected), expected);
    EXPECT_EQ(solver.resolveMixed(pivot, expected, right), expected);
}

TEST_F(LIAInterpolationTest, test_ResolveMixed_IntegerDivisibility) {
    /*
     * Pivot p := y <= x with fresh shared variable m = .mixed_<p>
     *
     * left:  2m <= r     right:  t <= 2m
     *
     * Over the integers, eliminating m must keep the parity information: the result is equivalent to
     * "there is an even number between t and r", i.e.  ceil(t/2) <= floor(r/2), not just  t <= r.
     */
    LASolver solver(config, logic);
    PTRef t = logic.mkIntVar("t");
    PTRef r = logic.mkIntVar("r");
    PTRef two = logic.mkIntConst(2);
    PTRef pivot = logic.mkLeq(y, x);
    PTRef m = logic.mkIntVar((".mixed_" + std::to_string(pivot.x)).c_str());
    PTRef twoM = logic.mkTimes(two, m);
    PTRef left = logic.mkLeq(twoM, r);
    PTRef right = logic.mkLeq(t, twoM);
    PTRef ceilHalfT = logic.mkNeg(logic.mkIntDiv(logic.mkNeg(t), two));
    PTRef expected = logic.mkLeq(ceilHalfT, logic.mkIntDiv(r, two));
    VerificationUtils verifier(logic);

    PTRef res = solver.resolveMixed(pivot, left, right);
    std::cout << logic.pp(res) << std::endl;
    EXPECT_TRUE(verifier.impliesInternal(res, expected));
    EXPECT_TRUE(verifier.impliesInternal(expected, res));
    // t <= r alone is weaker: t = r = 1 satisfies it, but there is no even number in [1, 1]
    EXPECT_FALSE(verifier.impliesInternal(logic.mkLeq(t, r), res));
}

}
