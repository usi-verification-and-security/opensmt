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
    std::string msg;
    ASSERT_TRUE(logic.typeCheck(ufun1, {uvar}, msg));
    ASSERT_TRUE(logic.typeCheck(ufun1, {uvar}, msg));
    ASSERT_FALSE(logic.typeCheck(ufun1, {vvar}, msg));
    ASSERT_FALSE(logic.typeCheck(ufun1, {}, msg));
    ASSERT_FALSE(logic.typeCheck(ufun1, {uvar, uvar}, msg));
}

TEST_F(TermTypecheckingTest, test_BinaryFun) {
    std::string msg;
    ASSERT_TRUE(logic.typeCheck(ufun2, {uvar, uvar}, msg));
    ASSERT_FALSE(logic.typeCheck(ufun2, {uvar, vvar}, msg));
    ASSERT_FALSE(logic.typeCheck(ufun2, {}, msg));
    ASSERT_FALSE(logic.typeCheck(ufun2, {uvar, uvar, uvar}, msg));
}

TEST_F(TermTypecheckingTest, test_MixedFun) {
    std::string msg;
    ASSERT_TRUE(logic.typeCheck(mixfun2, {uvar, vvar}, msg));
    ASSERT_FALSE(logic.typeCheck(mixfun2, {uvar, uvar}, msg));
    ASSERT_TRUE(logic.typeCheck(mixfun3, {uvar, vvar, uvar}, msg));
    ASSERT_FALSE(logic.typeCheck(mixfun3, {uvar, vvar, vvar}, msg));
}

TEST_F(TermTypecheckingTest, test_PairwiseAndChainable) {
    for (SymRef f: {chainableFun, pairwiseFun}) {
        std::string msg;
        ASSERT_TRUE(logic.typeCheck(f, {uvar, uvar}, msg));
        ASSERT_TRUE(logic.typeCheck(f, {uvar, uvar, uvar, uvar, uvar}, msg));
        ASSERT_FALSE(logic.typeCheck(f, {uvar}, msg));
        ASSERT_FALSE(logic.typeCheck(f, {}, msg));
        ASSERT_FALSE(logic.typeCheck(f, {uvar, vvar}, msg));
        ASSERT_FALSE(logic.typeCheck(f, {uvar, uvar, uvar, uvar, vvar}, msg));
    }
}

TEST_F(TermTypecheckingTest, test_AssociativeFun) {
    std::string msg;
    ASSERT_TRUE(logic.typeCheck(leftAssocFun, {uvar, vvar}, msg));
    ASSERT_TRUE(logic.typeCheck(leftAssocFun, {uvar, vvar, vvar, vvar}, msg));
    ASSERT_FALSE(logic.typeCheck(leftAssocFun, {}, msg));
    ASSERT_FALSE(logic.typeCheck(leftAssocFun, {uvar}, msg));
    ASSERT_FALSE(logic.typeCheck(leftAssocFun, {uvar, vvar, vvar, uvar}, msg));

    ASSERT_TRUE(logic.typeCheck(rightAssocFun, {vvar, uvar}, msg));
    ASSERT_TRUE(logic.typeCheck(rightAssocFun, {vvar, vvar, vvar, uvar}, msg));
    ASSERT_FALSE(logic.typeCheck(rightAssocFun, {}, msg));
    ASSERT_FALSE(logic.typeCheck(rightAssocFun, {vvar}, msg));
    ASSERT_FALSE(logic.typeCheck(rightAssocFun, {vvar, vvar, vvar, vvar}, msg));
}
