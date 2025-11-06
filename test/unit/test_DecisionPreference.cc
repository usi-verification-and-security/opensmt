/*
 *  Copyright (c) 2025, Tomas Kolarik <tomaqa@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include <api/Opensmt.h>
#include <gtest/gtest.h>

namespace opensmt {

class TestMainSolver : public MainSolver {
public:
    using MainSolver::MainSolver;

    friend class DecisionPreferenceTest;
};

class DecisionPreferenceTest : public ::testing::Test {
public:
    void init(Logic_t logic_t = Logic_t::QF_BOOL) {
        logic = std::make_unique<Logic>(logic_t);
        config = std::make_unique<SMTConfig>();
        config->setProduceModels();
        mainSolver = std::make_unique<TestMainSolver>(*logic, *config, "test");

        a = logic->mkBoolVar("a");
        b = logic->mkBoolVar("b");
        not_a = logic->mkNot(a);
        not_b = logic->mkNot(b);

        and_ab = logic->mkAnd(a, b);
        or_ab = logic->mkOr(a, b);
        xor_ab = logic->mkXor(a, b);
        eq_ab = logic->mkEq(a, b);
        impl_ab = logic->mkImpl(a, b);
        impl_ba = logic->mkImpl(b, a);

        and_nab = logic->mkAnd(not_a, b);
        and_anb = logic->mkAnd(a, not_b);
        and_nanb = logic->mkAnd(not_a, not_b);
        or_nanb = logic->mkOr(not_a, not_b);

        existingTotalCount = 0;
        boolVarTotalCount = 0;
        otherTotalCount = 0;
    }

    void checkPreferenceCount(std::size_t existingCount, std::size_t boolVarCount, std::size_t otherCount) const {
        EXPECT_EQ(mainSolver->existingDecisionPreferencesGivenToSMTSolverCount, existingCount);
        EXPECT_EQ(mainSolver->boolVarDecisionPreferencesGivenToSMTSolverCount, boolVarCount);
        EXPECT_EQ(mainSolver->otherDecisionPreferencesGivenToSMTSolverCount, otherCount);
    }

    void checkPreferenceIncCount(std::size_t existingIncCount, std::size_t boolVarIncCount, std::size_t otherIncCount) const {
        checkPreferenceCount(existingTotalCount += existingIncCount, boolVarTotalCount += boolVarIncCount, otherTotalCount += otherIncCount);
    }

    void checkBool(sstat expRes, lbool expValA = l_Undef, lbool expValB = l_Undef) {
        auto res = mainSolver->check();
        EXPECT_EQ(res, expRes);
        if (expRes != s_True) { return; }

        auto model = mainSolver->getModel();
        PTRef val_a = model->evaluate(a);
        PTRef val_b = model->evaluate(b);
        assert(val_a != PTRef_Undef);
        assert(val_b != PTRef_Undef);
        PTRef exp_val_a = lboolValToPTRef(expValA);
        PTRef exp_val_b = lboolValToPTRef(expValB);
        if (exp_val_a != PTRef_Undef) { EXPECT_EQ(val_a, exp_val_a); }
        if (exp_val_b != PTRef_Undef) { EXPECT_EQ(val_b, exp_val_b); }
    }

protected:
    PTRef lboolValToPTRef(lbool val) const {
        if (val == l_False) { return logic->getTerm_false(); }
        if (val == l_True) { return logic->getTerm_true(); }
        // return logic->getDefaultValuePTRef(logic->getSort_bool());
        return PTRef_Undef;
    }

    std::unique_ptr<Logic> logic;
    std::unique_ptr<SMTConfig> config;
    std::unique_ptr<TestMainSolver> mainSolver;

    PTRef a;
    PTRef b;
    PTRef not_a;
    PTRef not_b;

    PTRef and_ab;
    PTRef or_ab;
    PTRef xor_ab;
    PTRef eq_ab;
    PTRef impl_ab;
    PTRef impl_ba;

    PTRef and_nab;
    PTRef and_anb;
    PTRef and_nanb;
    PTRef or_nanb;

    std::size_t mutable existingTotalCount;
    std::size_t mutable boolVarTotalCount;
    std::size_t mutable otherTotalCount;
};

TEST_F(DecisionPreferenceTest, test_Unconstrained__DecisionPreferenceA) {
    init();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True);
    checkPreferenceIncCount(1, 1, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True);
    checkPreferenceIncCount(1, 1, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_Undef, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_Undef, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_Unconstrained__DecisionPreferenceNotA) {
    init();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True);
    checkPreferenceIncCount(1, 1, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True);
    checkPreferenceIncCount(1, 1, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_Undef, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_Undef, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_A__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(a);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True);
    checkPreferenceIncCount(1, 1, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_A__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(a);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True);
    checkPreferenceIncCount(1, 1, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_NotA__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(not_a);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False);
    checkPreferenceIncCount(1, 1, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_NotA__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(not_a);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False);
    checkPreferenceIncCount(1, 1, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_AB__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(and_ab);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_AB__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(and_ab);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAB__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(or_ab);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAB__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(or_ab);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_XorAB__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(xor_ab);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_XorAB__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(xor_ab);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_EqAB__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(eq_ab);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_EqAB__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(eq_ab);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplAB__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(impl_ab);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplAB__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(impl_ab);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplBA__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(impl_ba);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplBA__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(impl_ba);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_NotAB__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(and_nab);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_NotAB__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(and_nab);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_NotB__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(and_anb);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ANotB__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(and_anb);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_NotANotB__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(and_nanb);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_NotANotB__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(and_nanb);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrNotANotB__DecisionPreferenceA) {
    init();
    mainSolver->addAssertion(or_nanb);
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrNotANotB__DecisionPreferenceNotA) {
    init();
    mainSolver->addAssertion(or_nanb);
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

/////////////////////////////////////////////////////////////////////////////

// Adding more complex preferences that are however present in the asserted formulas

TEST_F(DecisionPreferenceTest, test_OrAndABOrAB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_ab, or_ab}));
    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotABOrAB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nab, or_ab}));
    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndANotBOrAB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_anb, or_ab}));
    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotANotBOrAB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nanb, or_ab}));
    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndABXorAB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_ab, xor_ab}));
    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotABXorAB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nab, xor_ab}));
    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndANotBXorAB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_anb, xor_ab}));
    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotANotBXorAB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nanb, xor_ab}));
    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndABEqAB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_ab, eq_ab}));
    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotABEqAB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nab, eq_ab}));
    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndANotBEqAB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_anb, eq_ab}));
    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotANotBEqAB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nanb, eq_ab}));
    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndABImplAB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_ab, impl_ab}));
    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotABImplAB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nab, impl_ab}));
    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndANotBImplAB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_anb, impl_ab}));
    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotANotBImplAB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nanb, impl_ab}));
    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndABImplBA__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_ab, impl_ba}));
    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotABImplBA__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nab, impl_ba}));
    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndANotBImplBA__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_anb, impl_ba}));
    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotANotBImplBA__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nanb, impl_ba}));
    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndABOrNotANotB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_ab, or_nanb}));
    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotABOrNotANotB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nab, or_nanb}));
    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndANotBOrNotANotB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_anb, or_nanb}));
    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAndNotANotBOrNotANotB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(logic->mkOr({and_nanb, or_nanb}));
    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(3, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

/////////////////////////////////////////////////////////////////////////////

// Adding more complex preferences that are *not* present in the asserted formulas

TEST_F(DecisionPreferenceTest, test_OrAB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(or_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_ab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(or_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(or_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_anb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrAB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(or_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nanb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_XorAB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(xor_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_ab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_XorAB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(xor_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_XorAB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(xor_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_anb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_XorAB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(xor_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nanb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_EqAB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(eq_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_ab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_EqAB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(eq_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_EqAB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(eq_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_anb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_EqAB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(eq_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nanb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplAB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(impl_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_ab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplAB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(impl_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplAB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(impl_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_anb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplAB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(impl_ab);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nanb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplBA__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(impl_ba);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_ab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplBA__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(impl_ba);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplBA__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(impl_ba);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_anb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_ImplBA__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(impl_ba);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nanb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_True, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrNotANotB__DecisionPreferenceAB) {
    init();
    mainSolver->addAssertion(or_nanb);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_ab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_ab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrNotANotB__DecisionPreferenceNotAB) {
    init();
    mainSolver->addAssertion(or_nanb);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nab);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nab);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrNotANotB__DecisionPreferenceANotB) {
    init();
    mainSolver->addAssertion(or_nanb);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_anb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_anb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_True, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

TEST_F(DecisionPreferenceTest, test_OrNotANotB__DecisionPreferenceNotANotB) {
    init();
    mainSolver->addAssertion(or_nanb);

    // Also check that it does not use already invalid assertions
    mainSolver->push();
    mainSolver->addAssertion(and_nanb);
    mainSolver->pop();

    mainSolver->addDecisionPreference(and_nanb);

    mainSolver->push();
    mainSolver->addDecisionPreference(a);
    mainSolver->addDecisionPreference(not_a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 1);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_a);
    mainSolver->addDecisionPreference(a);

    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->push();
    mainSolver->addDecisionPreference(b);
    mainSolver->addDecisionPreference(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addDecisionPreference(not_b);
    mainSolver->addDecisionPreference(b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(2, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(b);
    checkBool(s_True, l_False, l_True);
    checkPreferenceIncCount(0, 0, 0);

    mainSolver->pop();
    mainSolver->push();
    mainSolver->addAssertion(not_b);
    checkBool(s_True, l_False, l_False);
    checkPreferenceIncCount(0, 0, 0);
}

} // namespace opensmt
