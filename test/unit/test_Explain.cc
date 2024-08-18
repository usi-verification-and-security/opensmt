//
// Created by prova on 28.09.20.
//

#include <gtest/gtest.h>
#include <logics/Logic.h>
#include <tsolvers/egraph/EnodeStore.h>
#include <tsolvers/egraph/Explainer.h>

#include <utility>

namespace opensmt {

class UFExplainTest : public ::testing::Test {
    using PTERef = PTRefERefPair;
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

    UFExplainTest(): logic{Logic_t::QF_UF}, store(logic) {}
    virtual void SetUp() {
        ufsort = logic.declareUninterpretedSort("U");
        c0 = makeAndStorePTRef(logic.mkVar(ufsort, "c0"));
        c1 = makeAndStorePTRef(logic.mkVar(ufsort, "c1"));
        c2 = makeAndStorePTRef(logic.mkVar(ufsort, "c2"));

        SymRef f = logic.declareFun("f", ufsort, {ufsort, ufsort});

        f_c1_c0 = makeAndStorePTRef(logic.insertTerm(f, {c1.tr, c0.tr}));

        f_c2_c0 = makeAndStorePTRef(logic.insertTerm(f, {c2.tr, c0.tr}));
        f_f_c2_c0_c0 = makeAndStorePTRef(logic.insertTerm(f, {f_c2_c0.tr, c0.tr}));

    }
    EnodeStore& getStore() { return store; }
};

TEST_F(UFExplainTest, test_UFExplain) {

    PTRef eq1 = logic.mkEq(c2.tr, c1.tr);
    PTRef eq3 = logic.mkEq(f_f_c2_c0_c0.tr, c0.tr);
    PTRef eq7 = logic.mkEq(f_c1_c0.tr, c1.tr);

    Explainer explainer(store);
    explainer.storeExplanation(c2.er, c1.er, {eq1, l_True});
    explainer.storeExplanation(f_f_c2_c0_c0.er, c0.er, {eq3, l_True});
    explainer.storeExplanation(c1.er, f_c1_c0.er, {eq7, l_True});
    explainer.storeExplanation(f_c1_c0.er, f_f_c2_c0_c0.er, PtAsgn_Undef);
    ASSERT_THROW(explainer.explain(c1.er, f_c2_c0.er), InternalException);
    explainer.storeExplanation(f_c2_c0.er, f_c1_c0.er, PtAsgn_Undef);
    ASSERT_NO_THROW(explainer.explain(c1.er, f_c2_c0.er));
    ASSERT_NO_THROW(explainer.explain(c2.er, c0.er));
    std::cout << logic.pp(c2.tr) << " = " << logic.pp(c0.tr) << ": " << std::endl;
    for (PtAsgn pta : explainer.explain(c2.er, c0.er)) {
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

}
