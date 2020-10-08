//
// Created by Martin Blicha on 19.09.20.
//

#include <gtest/gtest.h>
#include <LRALogic.h>
#include "VerificationUtils.h"
#include <FarkasInterpolator.h>
#include <PartitionManager.h>

class LRAInterpolationTest : public ::testing::Test {
protected:
    LRAInterpolationTest(): logic{} {}
    virtual void SetUp() {
        x = logic.mkNumVar("x");
        y = logic.mkNumVar("y");
        x1 = logic.mkNumVar("x1");
        x2 = logic.mkNumVar("x2");
        x3 = logic.mkNumVar("x3");
        x4 = logic.mkNumVar("x4");
        y1 = logic.mkNumVar("y1");
        z1 = logic.mkNumVar("z1");
    }
    LRALogic logic;
    SMTConfig config;
    PTRef x, y, x1, x2, x3, x4, y1, y2, z1, z2, z3, z4, z5, z6, z7, z8;

    bool verifyInterpolant(PTRef itp, PartitionManager & pManager, ipartitions_t const & Amask) {
        return VerificationUtils(config, logic).verifyInterpolantInternal(pManager.getPartition(Amask, PartitionManager::part::A), pManager.getPartition(Amask, PartitionManager::part::B),itp);
    }

    bool verifyInterpolant(PTRef A, PTRef B, PTRef itp) {
        return VerificationUtils(config, logic).verifyInterpolantInternal(A, B, itp);
    }
};

TEST_F(LRAInterpolationTest, test_FarkasInterpolation_BothNonstrict){
    /*
     * A:   x1 + x2 <= 0
     *      -x2 - x3 <= 0
     *
     * B    x1 - x4 >= 1
     *      x4 - x3 >= 0
     */
    PTRef zero = logic.getTerm_NumZero();
    PTRef leq1 = logic.mkNumLeq(logic.mkNumPlus(x1,x2), zero);
    PTRef leq2 = logic.mkNumLeq(logic.mkNumNeg(logic.mkNumPlus(x2,x3)), zero);
    PTRef leq3 = logic.mkNumGeq(logic.mkNumMinus(x1,x4), logic.getTerm_NumOne());
    PTRef leq4 = logic.mkNumGeq(logic.mkNumMinus(x4,x3), zero);
    vec<PtAsgn> conflict {PtAsgn(leq1, l_True), PtAsgn(leq2, l_True), PtAsgn(leq3, l_True), PtAsgn(leq4, l_True)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::vector<opensmt::Real> coeffs {1,1,1,1};
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, I_A}, {conflict[1].tr, I_A}, {conflict[2].tr, I_B}, {conflict[3].tr, I_B}};
    PartitionManager dummy(logic);
    ipartitions_t dummyMask;
    FarkasInterpolator interpolator(logic, dummy, conflict, coeffs, dummyMask, &labels);
    PTRef farkasItp = interpolator.getFarkasInterpolant();
//    std::cout << logic.printTerm(farkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), farkasItp));
    PTRef dualFarkasItp = interpolator.getDualFarkasInterpolant();
//    std::cout << logic.printTerm(dualFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), dualFarkasItp));
    PTRef halfFarkasItp = interpolator.getFlexibleInterpolant(FastRational(1,2));
//    std::cout << logic.printTerm(halfFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), halfFarkasItp));
}

TEST_F(LRAInterpolationTest, test_FarkasInterpolation_Astrict){
    /*
     * A:   x1 + x2 < 0
     *      -x2 - x3 <= 0
     *
     * B    x1 - x4 >= 1
     *      x4 - x3 >= 0
     */
    PTRef zero = logic.getTerm_NumZero();
    PTRef leq1 = logic.mkNumLt(logic.mkNumPlus(x1,x2), zero);
    PTRef leq2 = logic.mkNumLeq(logic.mkNumNeg(logic.mkNumPlus(x2,x3)), zero);
    PTRef leq3 = logic.mkNumGeq(logic.mkNumMinus(x1,x4), logic.getTerm_NumOne());
    PTRef leq4 = logic.mkNumGeq(logic.mkNumMinus(x4,x3), zero);
    vec<PtAsgn> conflict {PtAsgn(logic.mkNot(leq1), l_False), PtAsgn(leq2, l_True), PtAsgn(leq3, l_True), PtAsgn(leq4, l_True)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::vector<opensmt::Real> coeffs {1,1,1,1};
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, I_A}, {conflict[1].tr, I_A}, {conflict[2].tr, I_B}, {conflict[3].tr, I_B}};
    PartitionManager dummy(logic);
    ipartitions_t dummyMask;
    FarkasInterpolator interpolator(logic, dummy, conflict, coeffs, dummyMask, &labels);
    PTRef farkasItp = interpolator.getFarkasInterpolant();
//    std::cout << logic.printTerm(farkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), farkasItp));
    PTRef dualFarkasItp = interpolator.getDualFarkasInterpolant();
//    std::cout << logic.printTerm(dualFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), dualFarkasItp));
    PTRef halfFarkasItp = interpolator.getFlexibleInterpolant(FastRational(1,2));
//    std::cout << logic.printTerm(halfFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), halfFarkasItp));
}

TEST_F(LRAInterpolationTest, test_FarkasInterpolation_Bstrict){
    /*
     * A:   x1 + x2 <= 0
     *      -x2 - x3 <= 0
     *
     * B    x1 - x4 > 1
     *      x4 - x3 >= 0
     */
    PTRef zero = logic.getTerm_NumZero();
    PTRef leq1 = logic.mkNumLeq(logic.mkNumPlus(x1,x2), zero);
    PTRef leq2 = logic.mkNumLeq(logic.mkNumNeg(logic.mkNumPlus(x2,x3)), zero);
    PTRef leq3 = logic.mkNumGt(logic.mkNumMinus(x1,x4), logic.getTerm_NumOne());
    PTRef leq4 = logic.mkNumGeq(logic.mkNumMinus(x4,x3), zero);
    vec<PtAsgn> conflict {PtAsgn(leq1, l_True), PtAsgn(leq2, l_True), PtAsgn(logic.mkNot(leq3), l_False), PtAsgn(leq4, l_True)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::vector<opensmt::Real> coeffs {1,1,1,1};
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, I_A}, {conflict[1].tr, I_A}, {conflict[2].tr, I_B}, {conflict[3].tr, I_B}};
    PartitionManager dummy(logic);
    ipartitions_t dummyMask;
    FarkasInterpolator interpolator(logic, dummy, conflict, coeffs, dummyMask, &labels);
    PTRef farkasItp = interpolator.getFarkasInterpolant();
//    std::cout << logic.printTerm(farkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), farkasItp));
    PTRef dualFarkasItp = interpolator.getDualFarkasInterpolant();
//    std::cout << logic.printTerm(dualFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), dualFarkasItp));
    PTRef halfFarkasItp = interpolator.getFlexibleInterpolant(FastRational(1,2));
//    std::cout << logic.printTerm(halfFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), halfFarkasItp));
}

TEST_F(LRAInterpolationTest, test_FarkasInterpolation_BothStrict){
    /*
     * A:   x1 + x2 < 0
     *      -x2 - x3 <= 0
     *
     * B    x1 - x4 > 1
     *      x4 - x3 >= 0
     */
    PTRef zero = logic.getTerm_NumZero();
    PTRef leq1 = logic.mkNumLt(logic.mkNumPlus(x1,x2), zero);
    PTRef leq2 = logic.mkNumLeq(logic.mkNumNeg(logic.mkNumPlus(x2,x3)), zero);
    PTRef leq3 = logic.mkNumGt(logic.mkNumMinus(x1,x4), logic.getTerm_NumOne());
    PTRef leq4 = logic.mkNumGeq(logic.mkNumMinus(x4,x3), zero);
    vec<PtAsgn> conflict {PtAsgn(logic.mkNot(leq1), l_False), PtAsgn(leq2, l_True), PtAsgn(logic.mkNot(leq3), l_False), PtAsgn(leq4, l_True)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::vector<opensmt::Real> coeffs {1,1,1,1};
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, I_A}, {conflict[1].tr, I_A}, {conflict[2].tr, I_B}, {conflict[3].tr, I_B}};
    PartitionManager dummy(logic);
    ipartitions_t dummyMask;
    FarkasInterpolator interpolator(logic, dummy, conflict, coeffs, dummyMask, &labels);
    PTRef farkasItp = interpolator.getFarkasInterpolant();
    std::cout << logic.printTerm(farkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), farkasItp));
    PTRef dualFarkasItp = interpolator.getDualFarkasInterpolant();
    std::cout << logic.printTerm(dualFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), dualFarkasItp));
    PTRef halfFarkasItp = interpolator.getFlexibleInterpolant(FastRational(1,2));
    std::cout << logic.printTerm(halfFarkasItp) << std::endl;
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd(leq1, leq2), logic.mkAnd(leq3, leq4), halfFarkasItp));
}

TEST_F(LRAInterpolationTest, test_AllInA){
    /*
     * A:   x1 + x2 <= 0
     *      -x2 - x3 <= 0
     *      x1 - x4 >= 1
     *      x4 - x3 >= 0
     */
    PTRef zero = logic.getTerm_NumZero();
    PTRef leq1 = logic.mkNumLeq(logic.mkNumPlus(x1,x2), zero);
    PTRef leq2 = logic.mkNumLeq(logic.mkNumNeg(logic.mkNumPlus(x2,x3)), zero);
    PTRef leq3 = logic.mkNumGeq(logic.mkNumMinus(x1,x4), logic.getTerm_NumOne());
    PTRef leq4 = logic.mkNumGeq(logic.mkNumMinus(x4,x3), zero);
    vec<PtAsgn> conflict {PtAsgn(leq1, l_True), PtAsgn(leq2, l_True), PtAsgn(leq3, l_True), PtAsgn(leq4, l_True)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::vector<opensmt::Real> coeffs {1,1,1,1};
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, I_A}, {conflict[1].tr, I_A}, {conflict[2].tr, I_A}, {conflict[3].tr, I_A}};
    PartitionManager dummy(logic);
    ipartitions_t dummyMask;
    FarkasInterpolator interpolator(logic, dummy, conflict, coeffs, dummyMask, &labels);
    PTRef farkasItp = interpolator.getFarkasInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3, leq4}), logic.getTerm_true(), farkasItp));
    EXPECT_EQ(farkasItp, logic.getTerm_false());
    PTRef dualFarkasItp = interpolator.getDualFarkasInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3, leq4}), logic.getTerm_true(), dualFarkasItp));
    EXPECT_EQ(dualFarkasItp, logic.getTerm_false());
    PTRef halfFarkasItp = interpolator.getFlexibleInterpolant(FastRational(1,2));
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3, leq4}), logic.getTerm_true(), halfFarkasItp));
    EXPECT_EQ(halfFarkasItp, logic.getTerm_false());
    PTRef decomposedFarkasItp = interpolator.getDecomposedInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3, leq4}), logic.getTerm_true(), decomposedFarkasItp));
    EXPECT_EQ(decomposedFarkasItp, logic.getTerm_false());
    PTRef dualDecomposedFarkasItp = interpolator.getDualDecomposedInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3, leq4}), logic.getTerm_true(), dualDecomposedFarkasItp));
    EXPECT_EQ(dualDecomposedFarkasItp, logic.getTerm_false());
}

TEST_F(LRAInterpolationTest, test_AllInB){
    /*
     * B:   x1 + x2 <= 0
     *      -x2 - x3 <= 0
     *      x1 - x4 >= 1
     *      x4 - x3 >= 0
     */
    PTRef zero = logic.getTerm_NumZero();
    PTRef leq1 = logic.mkNumLeq(logic.mkNumPlus(x1,x2), zero);
    PTRef leq2 = logic.mkNumLeq(logic.mkNumNeg(logic.mkNumPlus(x2,x3)), zero);
    PTRef leq3 = logic.mkNumGeq(logic.mkNumMinus(x1,x4), logic.getTerm_NumOne());
    PTRef leq4 = logic.mkNumGeq(logic.mkNumMinus(x4,x3), zero);
    vec<PtAsgn> conflict {PtAsgn(leq1, l_True), PtAsgn(leq2, l_True), PtAsgn(leq3, l_True), PtAsgn(leq4, l_True)};
    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
    std::vector<opensmt::Real> coeffs {1,1,1,1};
    std::map<PTRef, icolor_t> labels {{conflict[0].tr, I_B}, {conflict[1].tr, I_B}, {conflict[2].tr, I_B}, {conflict[3].tr, I_B}};
    PartitionManager dummy(logic);
    ipartitions_t dummyMask;
    FarkasInterpolator interpolator(logic, dummy, conflict, coeffs, dummyMask, &labels);
    PTRef farkasItp = interpolator.getFarkasInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.getTerm_true(), logic.mkAnd({leq1, leq2, leq3, leq4}), farkasItp));
    EXPECT_EQ(farkasItp, logic.getTerm_true());
    PTRef dualFarkasItp = interpolator.getDualFarkasInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.getTerm_true(), logic.mkAnd({leq1, leq2, leq3, leq4}), dualFarkasItp));
    EXPECT_EQ(dualFarkasItp, logic.getTerm_true());
    PTRef halfFarkasItp = interpolator.getFlexibleInterpolant(FastRational(1,2));
    EXPECT_TRUE(verifyInterpolant(logic.getTerm_true(), logic.mkAnd({leq1, leq2, leq3, leq4}), halfFarkasItp));
    EXPECT_EQ(halfFarkasItp, logic.getTerm_true());
    PTRef decomposedFarkasItp = interpolator.getDecomposedInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.getTerm_true(), logic.mkAnd({leq1, leq2, leq3, leq4}), decomposedFarkasItp));
    EXPECT_EQ(decomposedFarkasItp, logic.getTerm_true());
    PTRef dualDecomposedFarkasItp = interpolator.getDualDecomposedInterpolant();
    EXPECT_TRUE(verifyInterpolant(logic.getTerm_true(), logic.mkAnd({leq1, leq2, leq3, leq4}), dualDecomposedFarkasItp));
    EXPECT_EQ(dualDecomposedFarkasItp, logic.getTerm_true());
}

//TEST_F(LRAInterpolationTest, test_Decomposition_NonStrict){
//    /*
//     * A:   x1 >= 0
//     *      x2 - x1 >= 0
//     *      -x3 - x1 >= 0
//     * B:
//     *      x3 - x4 >= 0
//     *      -x4 - x2 >= 0
//     *      x4 >= 1
//     */
//    PTRef zero = logic.getTerm_NumZero();
//    PTRef leq1 = logic.mkNumGeq(x1, zero);
//    PTRef leq2 = logic.mkNumGeq(logic.mkNumMinus(x2,x1), zero);
//    PTRef leq3 = logic.mkNumGeq(logic.mkNumNeg(logic.mkNumPlus(x3,x1)), zero);
//
//    PTRef leq4 = logic.mkNumGeq(logic.mkNumMinus(x3,x4), zero);
//    PTRef leq5 = logic.mkNumGeq(logic.mkNumNeg(logic.mkNumPlus(x4,x2)), zero);
//    PTRef leq6 = logic.mkNumGeq(x4, logic.getTerm_NumOne());
//    vec<PtAsgn> conflict {PtAsgn(leq1, l_True), PtAsgn(leq2, l_True), PtAsgn(leq3, l_True),
//                          PtAsgn(leq4, l_True), PtAsgn(leq5, l_True), PtAsgn(leq6, l_True)};
//    ASSERT_TRUE(std::all_of(conflict.begin(), conflict.end(), [this](PtAsgn p) { return not logic.isNot(p.tr); }));
//    std::vector<opensmt::Real> coeffs {2,1,1,1,1,2};
//    std::map<PTRef, icolor_t> labels {{conflict[0].tr, I_A}, {conflict[1].tr, I_A}, {conflict[2].tr, I_A},
//                                      {conflict[3].tr, I_B}, {conflict[4].tr, I_B}, {conflict[5].tr, I_B}};
//    PartitionManager dummy(logic);
//    ipartitions_t dummyMask;
//    FarkasInterpolator interpolator(logic, dummy, conflict, coeffs, dummyMask, &labels);
//    PTRef decomposedFarkasItp = interpolator.getDecomposedInterpolant();
//    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3}), logic.mkAnd({leq4, leq5, leq6}), decomposedFarkasItp));
//    ASSERT_TRUE(logic.isAnd(decomposedFarkasItp));
//    EXPECT_EQ(decomposedFarkasItp, logic.mkAnd(logic.mkNumLeq(zero, x2), logic.mkNumLeq(zero, logic.mkNumNeg(x3))));
//    PTRef dualDecomposedFarkasItp = interpolator.getDualDecomposedInterpolant();
//    EXPECT_TRUE(verifyInterpolant(logic.mkAnd({leq1, leq2, leq3}), logic.mkAnd({leq4, leq5, leq6}), dualDecomposedFarkasItp));
//}