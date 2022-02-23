/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include <lasolver/LASolver.h>

class NameProtectionTest : public ::testing::Test {
public:
    NameProtectionTest() : arithLogic(opensmt::Logic_t::QF_LIA), ufLogic(opensmt::Logic_t::QF_UF), ufliaLogic(opensmt::Logic_t::QF_UFLIA) {}
    ArithLogic arithLogic;
    Logic ufLogic;
    ArithLogic ufliaLogic;
};

TEST_F(NameProtectionTest, test_NumberEscape) {
    PTRef numberOne = arithLogic.mkIntConst(1);
    ASSERT_EQ(arithLogic.pp(numberOne), "1");

    PTRef numberTen = arithLogic.mkIntConst(10);
    ASSERT_EQ(arithLogic.pp(numberTen), "10");

    PTRef numericVar = arithLogic.mkIntVar("10abc");
    ASSERT_EQ(arithLogic.pp(numericVar), "|10abc|");
}

TEST_F(NameProtectionTest, test_SymbolEscape) {
    PTRef symbolOne = ufLogic.mkVar(ufLogic.getSort_bool(), "1");
    ASSERT_EQ(ufLogic.pp(symbolOne), "|1|");

    PTRef symbolTen = ufLogic.mkVar(ufLogic.getSort_bool(), "10");
    ASSERT_EQ(ufLogic.pp(symbolTen), "|10|");

    PTRef symbolNumericStart = ufLogic.mkVar(ufLogic.getSort_bool(), "10ab");
    ASSERT_EQ(ufLogic.pp(symbolNumericStart), "|10ab|");
}

TEST_F(NameProtectionTest, test_SymbolExcapeMixed) {
    PTRef symbolOne = ufliaLogic.mkVar(ufliaLogic.getSort_bool(), "1");
    PTRef numberOne = ufliaLogic.mkIntConst(1);
    ASSERT_EQ(ufliaLogic.pp(symbolOne), "|1|");
    ASSERT_EQ(ufliaLogic.pp(numberOne), "1");

    SymRef functionOne = ufliaLogic.declareFun("1", ufliaLogic.getSort_int(), {ufliaLogic.getSort_int()});
    PTRef funSymbolOne = ufliaLogic.mkUninterpFun(functionOne, {ufliaLogic.mkIntConst(1)});
    ASSERT_EQ(ufliaLogic.pp(funSymbolOne), "(|1| 1)");
}

TEST_F(NameProtectionTest, test_ReservedWord) {
    PTRef symbolLet = ufLogic.mkVar(ufLogic.getSort_bool(), "let");
    ASSERT_EQ(ufLogic.pp(symbolLet), "|let|");
    PTRef symbolLet2 = arithLogic.mkVar(arithLogic.getSort_bool(), "let");
    ASSERT_EQ(arithLogic.pp(symbolLet2), "|let|");
    PTRef symbolLet3 = ufliaLogic.mkVar(ufliaLogic.getSort_bool(), "let");
    ASSERT_EQ(ufliaLogic.pp(symbolLet3), "|let|");
}