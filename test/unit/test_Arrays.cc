/*
* Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
*
*  SPDX-License-Identifier: MIT
*
*/

#include <gtest/gtest.h>
#include <logics/ArithLogic.h>
#include <api/MainSolver.h>

namespace opensmt {

class ArraysTest: public ::testing::Test {
public:
    ArraysTest()
        : logic(Logic_t::QF_ALIA), zero(logic.getTerm_IntZero()), one(logic.getTerm_IntOne())
    {}
    ArithLogic logic;
    PTRef zero;
    PTRef one;
};

TEST_F(ArraysTest, test_NoDuplicateSorts) {
    SRef s1 = logic.getArraySort(logic.getSort_int(), logic.getSort_int());
    SRef s2 = logic.getArraySort(logic.getSort_int(), logic.getSort_int());
    ASSERT_EQ(s1, s2);
}

TEST_F(ArraysTest, test_ReadOverWrite) {
    SRef sref = logic.getArraySort(logic.getSort_int(), logic.getSort_int());
    PTRef a = logic.mkVar(sref, "a");
    PTRef store = logic.mkStore({a, zero, one});
    PTRef select = logic.mkSelect({store, zero});

    SMTConfig config;
    MainSolver solver(logic, config, "solver");
    solver.insertFormula(logic.mkNot(logic.mkEq(select, one)));
    auto res = solver.check();
    ASSERT_EQ(res, s_False);
}

}
