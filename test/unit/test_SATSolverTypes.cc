/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include <minisat/core/SolverTypes.h>

namespace opensmt {

class SATSolverTypesTest : public ::testing::Test {
protected:
    ClauseAllocator ca;
};

TEST_F(SATSolverTypesTest, test_ClauseIterator) {
    vec<Lit> v(100);
    for (int i = 0; i < 100; i++) {
        v[i] = mkLit(i, i % 2);
    }
    CRef c = ca.alloc(v);
    int i = 0;
    for (Lit l : ca[c]) {
        ASSERT_EQ(l, v[i]);
        i++;
    }
}

}
