/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include <gtest/gtest.h>

#include <logics/Logic.h>
#include <api/MainSolver.h>
#include <common/VerificationUtils.h>
#include <tsolvers/lasolver/FarkasInterpolator.h>

namespace opensmt {

class ResolutionProofInterpolationTest : public ::testing::Test {
protected:
    ResolutionProofInterpolationTest(): logic{Logic_t::QF_UF} {}
    virtual void SetUp() {
        const char* msg;
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        solver = std::make_unique<MainSolver>(logic, config, "test");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("c");
        c = logic.mkBoolVar("b");
        na = logic.mkNot(a);
        nb = logic.mkNot(b);
        nc = logic.mkNot(c);

        A_part = logic.mkAnd(logic.mkOr(a, nb), logic.mkOr(a, b));
        B_part = logic.mkAnd(logic.mkOr(na, nc), logic.mkOr(na, c));

        solver->insertFormula(A_part);
        solver->insertFormula(B_part);
        auto res = solver->check();
        ASSERT_EQ(res, s_False);
    }
    Logic logic;
    SMTConfig config;
    std::unique_ptr<MainSolver> solver;
    PTRef a, b, c, na, nb, nc;
    PTRef A_part, B_part;

    bool verifyInterpolant(PTRef A, PTRef B, PTRef itp) {
        return VerificationUtils(logic).verifyInterpolantInternal(A, B, itp);
    }
};

TEST_F(ResolutionProofInterpolationTest, test_McMillanInterpolant) {
    config.setBooleanInterpolationAlgorithm(itp_alg_mcmillan);
    auto itpContext = solver->getInterpolationContext();
    vec<PTRef> itps;
    ipartitions_t A_mask = 1;
    itpContext->getSingleInterpolant(itps, A_mask);
    PTRef itp = itps.last();
//    std::cout << logic.pp(itp);
    ASSERT_TRUE(verifyInterpolant(A_part, B_part, itp));
}

TEST_F(ResolutionProofInterpolationTest, test_PudlakInterpolant) {
    config.setBooleanInterpolationAlgorithm(itp_alg_pudlak);
    auto itpContext = solver->getInterpolationContext();
    vec<PTRef> itps;
    ipartitions_t A_mask = 1;
    itpContext->getSingleInterpolant(itps, A_mask);
    PTRef itp = itps.last();
//    std::cout << logic.pp(itp);
    ASSERT_TRUE(verifyInterpolant(A_part, B_part, itp));
}

TEST_F(ResolutionProofInterpolationTest, test_McMillanPrimeInterpolant) {
    config.setBooleanInterpolationAlgorithm(itp_alg_mcmillanp);
    auto itpContext = solver->getInterpolationContext();
    vec<PTRef> itps;
    ipartitions_t A_mask = 1;
    itpContext->getSingleInterpolant(itps, A_mask);
    PTRef itp = itps.last();
//    std::cout << logic.pp(itp);
    ASSERT_TRUE(verifyInterpolant(A_part, B_part, itp));
}


class ResolutionProofInterpolationTestWithReduction : public ::testing::Test {
protected:
    ResolutionProofInterpolationTestWithReduction(): logic{Logic_t::QF_UF} {}
    virtual void SetUp() {
        const char* msg;
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
//        config.setOption(SMTConfig::o_verbosity, SMTOption(2), msg);
        solver = std::make_unique<MainSolver>(logic, config, "test");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        c = logic.mkBoolVar("c");
        d = logic.mkBoolVar("d");
        e = logic.mkBoolVar("e");
        na = logic.mkNot(a);
        nb = logic.mkNot(b);
        nc = logic.mkNot(c);
        nd = logic.mkNot(d);
        ne = logic.mkNot(e);

        A_part = logic.mkAnd({logic.mkOr(a, b), logic.mkOr(na,c)});
        B_part = logic.mkAnd({logic.mkOr(a, e), nd, logic.mkOr(d, ne), logic.mkOr(d, nc), logic.mkOr({na, nb, d})});

        solver->insertFormula(A_part);
        solver->insertFormula(B_part);
        auto res = solver->check();
        ASSERT_EQ(res, s_False);
    }
    Logic logic;
    SMTConfig config;
    std::unique_ptr<MainSolver> solver;
    PTRef a, b, c, d, e, na, nb, nc, nd, ne;
    PTRef A_part, B_part;

    bool verifyInterpolant(PTRef A, PTRef B, PTRef itp) {
        return VerificationUtils(logic).verifyInterpolantInternal(A, B, itp);
    }
};

TEST_F(ResolutionProofInterpolationTestWithReduction, test_InterpolationAfterReduction) {
    config.setBooleanInterpolationAlgorithm(itp_alg_mcmillan);
    config.setReduction(1);
    auto itpContext = solver->getInterpolationContext();
    vec<PTRef> itps;
    ipartitions_t A_mask = 1;
    itpContext->getSingleInterpolant(itps, A_mask);
    PTRef itp = itps.last();
    std::cout << logic.pp(itp);
    ASSERT_TRUE(verifyInterpolant(A_part, B_part, itp));
}

/*************** TESTS FOR INTERPOLATION FOR INCREMENTAL SOLVING *****************/
class ResolutionProofIncrementalInterpolationTest : public ::testing::Test {
protected:
    ResolutionProofIncrementalInterpolationTest(): logic{Logic_t::QF_UF} {}
    virtual void SetUp() {
        const char* msg;
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        solver = std::make_unique<MainSolver>(logic, config, "test");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("c");
        c = logic.mkBoolVar("b");
        na = logic.mkNot(a);
        nb = logic.mkNot(b);
        nc = logic.mkNot(c);

        A_part = logic.mkAnd(logic.mkOr(a, nb), logic.mkOr(a, b));
        B_part = logic.mkAnd(logic.mkOr(na, nc), logic.mkOr(na, c));

        solver->push();
        solver->insertFormula(A_part);
        solver->push();
        solver->insertFormula(B_part);
        auto res = solver->check();
        ASSERT_EQ(res, s_False);
    }
    Logic logic;
    SMTConfig config;
    std::unique_ptr<MainSolver> solver;
    PTRef a, b, c, na, nb, nc;
    PTRef A_part, B_part;

    bool verifyInterpolant(PTRef A, PTRef B, PTRef itp) {
        return VerificationUtils(logic).verifyInterpolantInternal(A, B, itp);
    }
};

TEST_F(ResolutionProofIncrementalInterpolationTest, test_McMillanInterpolant) {
    config.setBooleanInterpolationAlgorithm(itp_alg_mcmillan);
    auto itpContext = solver->getInterpolationContext();
    vec<PTRef> itps;
    ipartitions_t A_mask = 1;
    itpContext->getSingleInterpolant(itps, A_mask);
    PTRef itp = itps.last();
//    std::cout << logic.pp(itp);
    ASSERT_TRUE(verifyInterpolant(A_part, B_part, itp));
}

}
