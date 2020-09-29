//
// Created by prova on 28.09.20.
//

#include <gtest/gtest.h>
#include <EnodeStore.h>
#include <Logic.h>
#include <Explainer.h>

class UFExplainTest : public ::testing::Test {
protected:
    UFExplainTest(): logic{}, store(logic) {}
    virtual void SetUp() {
        ufsort = logic.declareSort("U", nullptr);
        PTRef c0 = logic.mkVar(ufsort, "c0");
        PTRef c1 = logic.mkVar(ufsort, "c1");
        PTRef c2 = logic.mkVar(ufsort, "c2");

        SymRef f = logic.declareFun("f", ufsort, {ufsort, ufsort}, nullptr, false);

        PTRef f_c1_c0 = logic.insertTerm(f, {c1, c0});
        eq1 = logic.mkEq(c1, f_c1_c0);

        PTRef f_c2_c0 = logic.insertTerm(f, {c2, c0});
        PTRef f_f_c2_c0_c0 = logic.insertTerm(f, {f_c2_c0, c0});
        eq3 = logic.mkEq(f_f_c2_c0_c0, c0);
        eq7 = logic.mkEq(f_c2_c0, c0);
    }
    Logic logic;
    EnodeStore store;

    SRef ufsort;
    PTRef eq1;
    PTRef eq3;
    PTRef eq7;
};

TEST_F(UFExplainTest, test_UFExplain) {
    //store.d
    //Explainer explainer(store);
    //explainer.expStoreExplanation()
}