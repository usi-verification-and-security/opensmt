//
// Created by Antti Hyvarinen on 14.11.21.
//

#include <gtest/gtest.h>
#include <Logic.h>

class TermTypecheckingTest: public ::testing::Test {
public:
    Logic logic;
    SRef usort = logic.declareUninterpretedSort("U");
    SRef vsort = logic.declareUninterpretedSort("V");
    PTRef uvar;
    PTRef vvar;
    SymRef ufun1;
    SymRef ufun2;
    SymRef mixfun2;
    SymRef mixfun3;
    SymRef chainableFun;
    SymRef pairwiseFun;
    SymRef leftAssocFun;
    SymRef rightAssocFun;
    TermTypecheckingTest()
        : logic{}
        , usort(logic.declareUninterpretedSort("U"))
        , vsort(logic.declareUninterpretedSort("V"))
        , uvar(logic.mkVar(usort, "u"))
        , vvar(logic.mkVar(vsort, "v"))
        , ufun1(logic.declareFun("uf1", usort, {usort}))
        , ufun2(logic.declareFun("uf2", usort, {usort, usort}))
        , mixfun2(logic.declareFun("mf2", usort, {usort, vsort}))
        , mixfun3(logic.declareFun("mf3", usort, {usort, vsort, usort}))
        , chainableFun(logic.declareFun_Chainable("cf", logic.getSort_bool(), {usort, usort}))
        , pairwiseFun(logic.declareFun_Pairwise("pf", logic.getSort_bool(), {usort, usort}))
        , leftAssocFun(logic.declareFun_LeftAssoc("lf", usort, {usort, vsort}))
        , rightAssocFun(logic.declareFun_RightAssoc("rf", usort, {vsort, usort}))
        {}
};

TEST_F(TermTypecheckingTest, test_UnaryFun) {
    ASSERT_NO_THROW(logic.mkUninterpFun(ufun1, {uvar}));
    ASSERT_THROW(logic.mkUninterpFun(ufun1, {vvar}), OsmtApiException);
    ASSERT_THROW(logic.mkUninterpFun(ufun1, {}), OsmtApiException);
    ASSERT_THROW(logic.mkUninterpFun(ufun1, {uvar, uvar}), OsmtApiException);
}

TEST_F(TermTypecheckingTest, test_BinaryFun) {
    ASSERT_NO_THROW(logic.mkUninterpFun(ufun2, {uvar, uvar}));
    ASSERT_THROW(logic.mkUninterpFun(ufun2, {uvar, vvar}), OsmtApiException);
    ASSERT_THROW(logic.mkUninterpFun(ufun2, {}), OsmtApiException);
    ASSERT_THROW(logic.mkUninterpFun(ufun2, {uvar, uvar, uvar}), OsmtApiException);
}

TEST_F(TermTypecheckingTest, test_MixedFun) {
    ASSERT_NO_THROW(logic.mkUninterpFun(mixfun2, {uvar, vvar}));
    ASSERT_THROW(logic.mkUninterpFun(mixfun2, {uvar, uvar}), OsmtApiException);
    ASSERT_NO_THROW(logic.mkUninterpFun(mixfun3, {uvar, vvar, uvar}));
    ASSERT_THROW(logic.mkUninterpFun(mixfun3, {uvar, vvar, vvar}), OsmtApiException);
}

TEST_F(TermTypecheckingTest, test_PairwiseAndChainable) {
    for (SymRef f: {chainableFun, pairwiseFun}) {
        ASSERT_NO_THROW(logic.mkUninterpFun(f, {uvar, uvar}));
        ASSERT_NO_THROW(logic.mkUninterpFun(f, {uvar, uvar, uvar, uvar, uvar}));
        ASSERT_THROW(logic.mkUninterpFun(f, {uvar}), OsmtApiException);
        ASSERT_THROW(logic.mkUninterpFun(f, {}), OsmtApiException);
        ASSERT_THROW(logic.mkUninterpFun(f, {uvar, vvar}), OsmtApiException);
        ASSERT_THROW(logic.mkUninterpFun(f, {uvar, uvar, uvar, uvar, vvar}), OsmtApiException);
    }
}

TEST_F(TermTypecheckingTest, test_AssociativeFun) {
    PTRef test = logic.mkUninterpFun(chainableFun, {uvar, uvar});
    Pterm & t = logic.getPterm(test);
    std::for_each(t.begin(), t.end()-1, [&](PTRef tr) { std::cout << logic.pp(tr) <<"\n"; });
    std::cout << std::endl;
    for (PTRef ch : logic.getPterm(test)) {
        std::cout << logic.pp(ch) << std::endl;
    }
    ASSERT_NO_THROW(logic.mkUninterpFun(leftAssocFun, {uvar, vvar}));
    ASSERT_NO_THROW(logic.mkUninterpFun(leftAssocFun, {uvar, vvar, vvar, vvar}));
    ASSERT_THROW(logic.mkUninterpFun(leftAssocFun, {}), OsmtApiException);
    ASSERT_THROW(logic.mkUninterpFun(leftAssocFun, {uvar}), OsmtApiException);
    ASSERT_THROW(logic.mkUninterpFun(leftAssocFun, {uvar, vvar, vvar, uvar}), OsmtApiException);

    ASSERT_NO_THROW(logic.mkUninterpFun(rightAssocFun, {vvar, uvar}));
    ASSERT_NO_THROW(logic.mkUninterpFun(rightAssocFun, {vvar, vvar, vvar, uvar}));
    ASSERT_THROW(logic.mkUninterpFun(rightAssocFun, {}), OsmtApiException);
    ASSERT_THROW(logic.mkUninterpFun(rightAssocFun, {vvar}), OsmtApiException);
    ASSERT_THROW(logic.mkUninterpFun(rightAssocFun, {vvar, vvar, vvar, vvar}), OsmtApiException);
}
