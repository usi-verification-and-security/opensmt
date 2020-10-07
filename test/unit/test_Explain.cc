//
// Created by prova on 28.09.20.
//

#include <gtest/gtest.h>
#include <EnodeStore.h>
#include <Logic.h>
#include <Explainer.h>
#include <utility>

class UFExplainTest : public ::testing::Test {
    using PTERef = std::pair<PTRef,ERef>;
    SRef ufsort;
    PTERef makeAndStorePTRef(PTRef tr) { vec<PTERef> v = store.constructTerm(tr); assert(v.size() == 1); return v[0]; }

protected:
    Logic logic;
    EnodeStore store;
    PTERef c0;
    PTERef c1;
    PTERef c2;
    PTERef f_c1_c0;
    PTERef f_c2_c0;
    PTERef f_f_c2_c0_c0;

    UFExplainTest(): logic{}, store(logic) {}
    virtual void SetUp() {
        ufsort = logic.declareSort("U", nullptr);
        c0 = makeAndStorePTRef(logic.mkVar(ufsort, "c0"));
        c1 = makeAndStorePTRef(logic.mkVar(ufsort, "c1"));
        c2 = makeAndStorePTRef(logic.mkVar(ufsort, "c2"));

        SymRef f = logic.declareFun("f", ufsort, {ufsort, ufsort}, nullptr, false);

        f_c1_c0 = makeAndStorePTRef(logic.insertTerm(f, {c1.first, c0.first}));

        f_c2_c0 = makeAndStorePTRef(logic.insertTerm(f, {c2.first, c0.first}));
        f_f_c2_c0_c0 = makeAndStorePTRef(logic.insertTerm(f, {f_c2_c0.first, c0.first}));

    }
    EnodeStore& getStore() { return store; }
};

TEST_F(UFExplainTest, test_UFExplain) {

    PTRef eq1 = logic.mkEq(c2.first, c1.first);
    PTRef eq3 = logic.mkEq(f_f_c2_c0_c0.first, c0.first);
    PTRef eq7 = logic.mkEq(f_c1_c0.first, c1.first);

    Explainer explainer(store);
    explainer.storeExplanation(c2.second, c1.second, {eq1, l_True});
    explainer.storeExplanation(f_f_c2_c0_c0.second, c0.second, {eq3, l_True});
    explainer.storeExplanation(c1.second, f_c1_c0.second, {eq7, l_True});
    explainer.storeExplanation(f_c1_c0.second, f_f_c2_c0_c0.second, PtAsgn_Undef);
    ASSERT_THROW(explainer.explain(c1.second, f_c2_c0.second), OsmtInternalException);
    explainer.storeExplanation(f_c2_c0.second, f_c1_c0.second, PtAsgn_Undef);
    ASSERT_NO_THROW(explainer.explain(c1.second, f_c2_c0.second));
    ASSERT_NO_THROW(explainer.explain(c2.second, c0.second));
    std::cout << logic.pp(c2.first) << " = " << logic.pp(c0.first) << ": " << std::endl;
    for (PtAsgn pta : explainer.explain(c2.second, c0.second)) {
        std::cout << "  " << logic.pp(pta.tr) << std::endl;
    }

    for (auto ptRefPair : explainer.getCongruences()) {
        PTRef x = ptRefPair.first;
        PTRef y = ptRefPair.second;
        std::cout << logic.pp(x) << " = " << logic.pp(y) << std::endl;
        for (PtAsgn pta : explainer.explain(store.getERef(x), store.getERef(y))) {
            std::cout << "  " << logic.pp(pta.tr) << std::endl;
        }
    }

}