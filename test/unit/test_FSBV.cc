/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */


#include <gtest/gtest.h>
#include <FSBVLogic.h>

#include <memory>
#include "BitBlasterRewriter.h"

class FSBVTest : public ::testing::Test {
protected:
    FSBVTest(): logic{opensmt::Logic_t::QF_BV} {}

    FSBVLogic logic;
};

TEST_F(FSBVTest, test_createConst) {
    PTRef x = logic.mkBVConst(32, 123);
    SRef xsort = logic.getSortRef(x);
    std::string binaryRepresentation = logic.pp(x);
    std::cout << binaryRepresentation << std::endl;
    ASSERT_EQ(binaryRepresentation, "#b00000000000000000000000001111011");
    std::cout << logic.printSort(xsort) << std::endl;
    ASSERT_NE(x, PTRef_Undef);

    PTRef y = logic.mkBVConst(16, 123);
    SRef ysort = logic.getSortRef(y);
    binaryRepresentation = logic.pp(y);
    std::cout << binaryRepresentation << std::endl;
    ASSERT_EQ(binaryRepresentation, "#b0000000001111011");
    std::cout << logic.printSort(ysort) << std::endl;

    PTRef z = logic.mkBVConst(16, 124);
    SRef zsort = logic.getSortRef(z);
    binaryRepresentation = logic.pp(z);
    std::cout << binaryRepresentation << std::endl;
    ASSERT_EQ(binaryRepresentation, "#b0000000001111100");
    std::cout << logic.printSort(zsort) << std::endl;
    ASSERT_NE(y, z);
    ASSERT_EQ(ysort, zsort);

    PTRef char1 = logic.mkBVConst(8, 1);
    PTRef char257 = logic.mkBVConst(8, 257);
    binaryRepresentation = logic.pp(char1);
    ASSERT_EQ(binaryRepresentation, "#b00000001");
    std::cout << binaryRepresentation << std::endl;
    binaryRepresentation = logic.pp(char257);
    ASSERT_EQ(binaryRepresentation, "#b00000001");
    std::cout << binaryRepresentation << std::endl;

//    x = logic.mkBVConstFromHex("#0000007B");
}

TEST_F(FSBVTest, test_createVar) {
    PTRef c8 = logic.mkBVVar(8, "v8");
    PTRef c9 = logic.mkBVVar(9, "v9");
    ASSERT_THROW(logic.mkEq(c8, c9), OsmtApiException);
    PTRef c9_ = logic.mkBVVar(9, "w9");
    ASSERT_NO_THROW(logic.mkEq(c9, c9_));
}

TEST_F(FSBVTest, test_mkAdd) {
    PTRef a8 = logic.mkBVVar(8, "a8");
    PTRef a9 = logic.mkBVVar(9, "a9");
    ASSERT_THROW(logic.mkBVAdd(a8, a9), OsmtApiException);
    PTRef b8 = logic.mkBVVar(8, "b8");
    PTRef add8 = logic.mkBVAdd(a8, b8);
    ASSERT_EQ(logic.getSortRef(add8), logic.getSortRef(b8));

    BitBlasterRewriter bitBlaster(logic);
    PTRef sum = logic.mkBVAdd(logic.mkBVConst(8, 10), logic.mkBVConst(8, 10));
    PTRef res = bitBlaster.rewrite(logic.mkEq(sum, logic.mkBVConst(8, 20)));
    ASSERT_EQ(res, logic.getTerm_true());
    res = bitBlaster.rewrite(logic.mkEq(sum, logic.mkBVConst(8, 21)));
    ASSERT_EQ(res, logic.getTerm_false());
}

TEST_F(FSBVTest, test_mkConcat) {
    PTRef a4 = logic.mkBVVar(4, "a4");
    PTRef a5 = logic.mkBVVar(5, "a5");
    PTRef conc = logic.mkBVConcat(a4, a5);
    std::cout << logic.pp(conc) << std::endl;
    ASSERT_NE(conc, PTRef_Undef);
    BitBlasterRewriter bitBlaster(logic);
    PTRef c1 = logic.mkBVConst(4, 0);
    PTRef c2 = logic.mkBVConst(3, 7);
    conc = logic.mkBVConcat(c1, c2);
    PTRef eq = logic.mkEq(conc, logic.mkBVConst(7, 7));
    std::cout << logic.pp(eq) << std::endl;
    PTRef res = bitBlaster.rewrite(logic.mkEq(conc, logic.mkBVConst(7, 7)));
    ASSERT_EQ(res, logic.getTerm_true());
}

TEST_F(FSBVTest, test_mkNeg) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef neg_a = logic.mkBVNeg(a);
    ASSERT_NE(a, PTRef_Undef);
    std::cout << logic.pp(neg_a) << std::endl;
    PTRef c = logic.mkBVConst(16, 1);
    PTRef neg_c = logic.mkBVNeg(c);
    PTRef eq = logic.mkEq(neg_c, logic.mkBVConst(16, 65535));
    std::cout << logic.pp(eq) << std::endl;
    BitBlasterRewriter bitBlasterRewriter(logic);
    ASSERT_EQ(logic.getTerm_true(), bitBlasterRewriter.rewrite(eq));
}

TEST_F(FSBVTest, test_mkNot) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef not_a = logic.mkBVNot(a);
    ASSERT_NE(a, PTRef_Undef);
    std::cout << logic.pp(not_a) << std::endl;
    PTRef c = logic.mkBVConst(4, 0);
    PTRef not_c = logic.mkBVNot(c);
    PTRef eq = logic.mkEq(not_c, logic.mkBVConst(4, 1));
    std::cout << logic.pp(eq) << std::endl;
    BitBlasterRewriter bitBlasterRewriter(logic);
    ASSERT_EQ(bitBlasterRewriter.rewrite(eq), logic.getTerm_true());
}

TEST_F(FSBVTest, test_mkFlip) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef not_a = logic.mkBVNot(a);
    ASSERT_NE(a, PTRef_Undef);
    std::cout << logic.pp(not_a) << std::endl;
    PTRef c = logic.mkBVConst(4, 0);
    PTRef not_c = logic.mkBVFlip(c);
    PTRef eq = logic.mkEq(not_c, logic.mkBVConst(4, 15));
    std::cout << logic.pp(eq) << std::endl;
    BitBlasterRewriter bitBlasterRewriter(logic);
    ASSERT_EQ(bitBlasterRewriter.rewrite(eq), logic.getTerm_true());
}

TEST_F(FSBVTest, test_mkAnd) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef b = logic.mkBVVar(16, "b");
    PTRef and_a_b = logic.mkBVAnd(a, b);
    ASSERT_NE(and_a_b, PTRef_Undef);
    std::cout << logic.pp(and_a_b) << std::endl;
    PTRef c1 = logic.mkBVConst(4, 15);
    PTRef c2 = logic.mkBVConst(4, 14);
    PTRef and_ = logic.mkBVAnd(c1, c2);
    PTRef eq = logic.mkEq(and_, c2);
    BitBlasterRewriter bitBlasterRewriter(logic);
    ASSERT_EQ(bitBlasterRewriter.rewrite(eq), logic.getTerm_true());
}

TEST_F(FSBVTest, test_mkOr) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef b = logic.mkBVVar(16, "b");
    PTRef or_a_b = logic.mkBVOr(a, b);
    ASSERT_NE(or_a_b, PTRef_Undef);
    std::cout << logic.pp(or_a_b) << std::endl;
    PTRef c1 = logic.mkBVConst(4, 15);
    PTRef c2 = logic.mkBVConst(4, 14);
    PTRef or_ = logic.mkBVOr(c1, c2);
    PTRef eq = logic.mkEq(or_, c1);
    BitBlasterRewriter bitBlasterRewriter(logic);
    ASSERT_EQ(bitBlasterRewriter.rewrite(eq), logic.getTerm_true());
}

TEST_F(FSBVTest, test_mkMul) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef b = logic.mkBVVar(16, "b");
    PTRef mul_a_b = logic.mkBVMul(a, b);
    ASSERT_NE(mul_a_b, PTRef_Undef);
    std::cout << logic.pp(mul_a_b) << std::endl;

    BitBlasterRewriter bitBlaster(logic);
    PTRef mul = logic.mkBVMul(logic.mkBVConst(8, 10), logic.mkBVConst(8, 2));
    PTRef res = bitBlaster.rewrite(logic.mkEq(mul, logic.mkBVConst(8, 20)));
    ASSERT_EQ(res, logic.getTerm_true());
    res = bitBlaster.rewrite(logic.mkEq(mul, logic.mkBVConst(8, 21)));
    ASSERT_EQ(res, logic.getTerm_false());
}

TEST_F(FSBVTest, test_mkUdiv) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef b = logic.mkBVVar(16, "b");
    PTRef udiv_a_b = logic.mkBVUdiv(a, b);
    ASSERT_NE(udiv_a_b, PTRef_Undef);
    std::cout << logic.pp(udiv_a_b) << std::endl;
    PTRef c1 = logic.mkBVConst(8, 3);
    PTRef c2 = logic.mkBVConst(8, 2);
    PTRef div = logic.mkBVUdiv(c1, c2);
    PTRef eq = logic.mkEq(div, logic.mkBVConst(8, 1));
    ASSERT_EQ(BitBlasterRewriter(logic).rewrite(eq), logic.getTerm_true());
    div = logic.mkBVUdiv(c1, logic.mkBVConst(8, 0));
    std::cout << logic.pp(div) << std::endl;
    eq = logic.mkEq(div, logic.mkBVConst(8, 1));
    ASSERT_EQ(BitBlasterRewriter(logic).rewrite(eq), logic.getTerm_true());
}

TEST_F(FSBVTest, test_mkUrem) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef b = logic.mkBVVar(16, "b");
    PTRef urem_a_b = logic.mkBVUrem(a, b);
    ASSERT_NE(urem_a_b, PTRef_Undef);
    std::cout << logic.pp(urem_a_b) << std::endl;

    PTRef c1 = logic.mkBVConst(8, 3);
    PTRef c2 = logic.mkBVConst(8, 2);
    PTRef rem = logic.mkBVUrem(c1, c2);
    PTRef eq = logic.mkEq(rem, logic.mkBVConst(8, 1));
    ASSERT_EQ(BitBlasterRewriter(logic).rewrite(eq), logic.getTerm_true());
    rem = logic.mkBVUrem(c1, logic.mkBVConst(8, 0));
    eq = logic.mkEq(rem, c1);
    ASSERT_EQ(BitBlasterRewriter(logic).rewrite(eq), logic.getTerm_true());
}


TEST_F(FSBVTest, test_mkSHL) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef b = logic.mkBVVar(16, "b");
    PTRef shl = logic.mkBVShl(a, b);
    ASSERT_NE(shl, PTRef_Undef);
    std::cout << logic.pp(shl) << std::endl;

    PTRef c1 = logic.mkBVConst(8, 1);
    PTRef c2 = logic.mkBVConst(8, 2);
    shl = logic.mkBVShl(c1, c2);
    PTRef eq = logic.mkEq(shl, logic.mkBVConst(8, 4));
    ASSERT_EQ(BitBlasterRewriter(logic).rewrite(eq), logic.getTerm_true());
}

TEST_F(FSBVTest, test_mkLSHR) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef b = logic.mkBVVar(16, "b");
    PTRef lshr = logic.mkBVLshr(a, b);
    ASSERT_NE(lshr, PTRef_Undef);
    std::cout << logic.pp(lshr) << std::endl;

    PTRef c1 = logic.mkBVConst(8, 4);
    PTRef c2 = logic.mkBVConst(8, 2);
    lshr = logic.mkBVLshr(c1, c2);
    PTRef eq = logic.mkEq(lshr, logic.mkBVConst(8, 1));
    ASSERT_EQ(BitBlasterRewriter(logic).rewrite(eq), logic.getTerm_true());
}

TEST_F(FSBVTest, test_mkULT) {
    PTRef a = logic.mkBVVar(16, "a");
    PTRef b = logic.mkBVVar(16, "b");
    PTRef ult = logic.mkBVUlt(a, b);
    ASSERT_NE(ult, PTRef_Undef);
    std::cout << logic.pp(ult) << std::endl;

    BitBlasterRewriter bitBlaster(logic);
    PTRef res = bitBlaster.rewrite(logic.mkBVUlt(logic.mkBVConst(8, 1), logic.mkBVConst(8, 2)));
    ASSERT_EQ(res, logic.getTerm_true());
    res = bitBlaster.rewrite(logic.mkBVUlt(logic.mkBVConst(8, 2), logic.mkBVConst(8, 2)));
    ASSERT_EQ(res, logic.getTerm_false());
}
