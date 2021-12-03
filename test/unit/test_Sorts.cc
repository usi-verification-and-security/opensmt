/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */


#include <gtest/gtest.h>
#include <Logic.h>
#include <SSort.h>

class SortTest : public ::testing::Test {
protected:
    SortTest(): logic{opensmt::Logic_t::QF_UF} {}
    Logic logic;
};

TEST_F(SortTest, test_indexedSort) {
    SRef fooSort = logic.getSort(logic.declareSortSymbol({"Foo", 0}), {});
    SRef barSort = logic.getSort(logic.declareSortSymbol({"Bar", 0}), {});
    SRef indexedSort = logic.getSort(logic.getSortSymIndexed(), {fooSort, barSort});
    ASSERT_NE(indexedSort, SRef_Undef);
    std::cout << logic.printSort(indexedSort) << std::endl;

    PTRef foo = logic.mkConst(fooSort, "foo");
    PTRef bar = logic.mkConst(barSort, "bar");
    std::cout << logic.pp(foo) << std::endl;
    std::cout << logic.pp(bar) << std::endl;

    SRef indexedSort2 = logic.getSort(logic.getSortSymIndexed(), {barSort, fooSort});
    ASSERT_NE(indexedSort2, indexedSort);
    std::cout << logic.printSort(indexedSort2) << std::endl;

    SRef quuxSort = logic.getSort(logic.declareSortSymbol({"Quux", 0}), {});
    SRef frobbozSort = logic.getSort(logic.declareSortSymbol({"Frobboz", 0}), {});
    SRef indexedSort3 = logic.getSort(logic.getSortSymIndexed(), {quuxSort, frobbozSort});
    ASSERT_NE(indexedSort, indexedSort3);
    std::cout << logic.printSort(indexedSort3) << std::endl;
}

TEST_F(SortTest, test_parametricSort) {
    SortSymbol symbolU("U", 1);
    logic.declareSortSymbol(std::move(symbolU));
    SortSymbol symbolV("V", 0);
    logic.declareSortSymbol(std::move(symbolV));
    SortSymbol symbolW("W", 0);
    logic.declareSortSymbol(std::move(symbolW));

    SortSymbol symbolV2("V", 0);
    SSymRef symbolRefV;
    bool rval = logic.peekSortSymbol(symbolV2, symbolRefV);
    ASSERT_TRUE(rval);
    SRef sortV = logic.getSort(symbolRefV, {});
    ASSERT_NE(sortV, SRef_Undef);

    SortSymbol symbolW2("W", 0);
    SSymRef symbolRefW;
    rval = logic.peekSortSymbol(symbolW2, symbolRefW);
    ASSERT_TRUE(rval);
    SRef sortW = logic.getSort(symbolRefW, {});
    ASSERT_NE(sortW, SRef_Undef);

    SortSymbol symbolU2("U", 1);
    SSymRef symbolRefU;
    rval = logic.peekSortSymbol(symbolU2, symbolRefU);
    ASSERT_TRUE(rval);
    SRef sortU_V = logic.getSort(symbolRefU, {sortV});
    std::cout << logic.printSort(sortU_V) << std::endl;
    SRef sortU_W = logic.getSort(symbolRefU, {sortW});
    std::cout << logic.printSort(sortU_V) << std::endl;
    std::cout << logic.printSort(sortU_W) << std::endl;

    ASSERT_NE(sortU_V, SRef_Undef);
    ASSERT_NE(sortU_W, SRef_Undef);

    logic.declareFun("a", sortU_V, {});
    logic.declareFun("b", sortU_W, {});

}
