/*
*  Copyright (c) 2019-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
*  Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
*
*  SPDX-License-Identifier: MIT
*/

#include <gtest/gtest.h>
#include <tsolvers/lasolver/Simplex.h>
#include <options/SMTConfig.h>
#include <tsolvers/lasolver/LABounds.h>
#include <tsolvers/lasolver/LAVar.h>

namespace opensmt {

TEST(Simplex_test, test_ops_in_Simplex)
{
    SMTConfig c;
    LAVarStore vs;

    LVRef x = vs.getNewVar();
    LVRef y = vs.getNewVar();

    LVRef y_minus_x = vs.getNewVar();
    auto p_y_minus_x = std::make_unique<PolynomialT<LVRef>>();

    p_y_minus_x->addTerm(x, -1);
    p_y_minus_x->addTerm(y, 1);

    LABoundStore bs(vs);

    Delta zero = Delta(0);
    Delta one = Delta(1);
    LABoundStore::BoundInfo x_strict_0   = bs.allocBoundPair(x, { Delta(0, -1), zero }); // x < 0 and x >= 0
    LABoundStore::BoundInfo y_strict_0   = bs.allocBoundPair(y, { Delta(0, -1), zero }); // y < 0 and y >= 0
//    LABoundStore::BoundInfo x_nostrict_0 = bs.allocBoundPair(x, 0, false); // x <= 0 and x > 0
//    LABoundStore::BoundInfo y_nostrict_0 = bs.allocBoundPair(y, 0, false); // y <= 0 and y > 0

    LABoundStore::BoundInfo x_strict_1   = bs.allocBoundPair(x, { Delta(1, -1), one }); // x < 1 and x >= 1
    LABoundStore::BoundInfo x_nostrict_1 = bs.allocBoundPair(x, { one, Delta(1, 1) }); // x <= 1 and x > 1
    LABoundStore::BoundInfo y_strict_1   = bs.allocBoundPair(y, { Delta(1, -1), one }); // y < 1 and y >= 1
    LABoundStore::BoundInfo y_nostrict_1 = bs.allocBoundPair(y, { one, Delta(1, 1) }); // y <= 1 and y > 1

    LABoundStore::BoundInfo y_minus_x_nostrict_0  = bs.allocBoundPair(y_minus_x, { zero, Delta(0, 1) });   // y - x <= 0 and y - x > 0
    LABoundStore::BoundInfo y_minus_x_nostrict_1  = bs.allocBoundPair(y_minus_x, { one, Delta(1, 1) });   // y - x - 1 <= 0
    //LABoundStore::BoundInfo y_minus_x_strict_0    = bs.allocBoundPair(y_minus_x, 0, true);    // y - x < 0 and y - x >= 0
    //LABoundStore::BoundInfo y_minus_x_strict_m1   = bs.allocBoundPair(y_minus_x, -1, true);   // y - x + 1 <  0
    //LABoundStore::BoundInfo y_minus_x_nostrict_m1 = bs.allocBoundPair(y_minus_x, -1, false);  // y - x + 1 <= 0
    //LABoundStore::BoundInfo y_minus_x_strict_1    = bs.allocBoundPair(y_minus_x, 1, true);    // y - x - 1 <  0


    bs.buildBounds();

    Simplex s(bs);

    s.newNonbasicVar(x);
    s.newNonbasicVar(y);
    s.newRow(y_minus_x, std::move(p_y_minus_x));

    s.initModel();

    Simplex::Explanation ex = s.checkSimplex();
    ASSERT_EQ(ex.size(), 0);

    Real d = s.computeDelta();
    Delta x_val = s.getValuation(x);
    std::cout << x_val.R() + x_val.D() * d << '\n';
    Delta y_val = s.getValuation(y);
    std::cout << y_val.R() + y_val.D() * d << '\n';
    Delta sum = s.getValuation(y_minus_x);
    std::cout << sum.R() + sum.D() * d << '\n';

    s.assertBound(x_strict_0.lb);
    s.assertBound(y_strict_0.lb);

    s.pushBacktrackPoint();

    s.assertBound(x_strict_1.ub);
    s.assertBound(y_strict_1.ub);

    ex = s.checkSimplex();
    ASSERT_EQ(ex.size(), 0);
    d = s.computeDelta();
    x_val = s.getValuation(x);
    std::cout << x_val.R() + x_val.D() * d << '\n';
    y_val = s.getValuation(y);
    std::cout << y_val.R() + y_val.D() * d << '\n';
    sum = s.getValuation(y_minus_x);
    std::cout << sum.R() + sum.D() * d << '\n';

    ex = s.assertBound(y_minus_x_nostrict_1.lb);
    ASSERT_EQ(ex.size(), 0); // not detectable at this point
    ex = s.checkSimplex();
    ASSERT_EQ(ex.size(), 3);

    s.popBacktrackPoint();
    s.finalizeBacktracking();

    s.assertBound(y_minus_x_nostrict_0.lb);
    s.assertBound(x_nostrict_1.lb);
    s.assertBound(y_nostrict_1.lb);
    ex = s.checkSimplex();
    ASSERT_EQ(ex.size(), 0);
    d = s.computeDelta();
    x_val = s.getValuation(x);
    std::cout << "x = " << x_val.R() + x_val.D() * d << '\n';
    y_val = s.getValuation(y);
    std::cout << "y = " << y_val.R() + y_val.D() * d << '\n';
    sum = s.getValuation(y_minus_x);
    std::cout << "y - x = " << sum.R() + sum.D() * d << std::endl;
}

TEST(Simplex_test, test_Assignment)
{
    SMTConfig c;
    LAVarStore vs;

    LVRef x = vs.getNewVar();
    LVRef y = vs.getNewVar();

    LVRef y_minus_x = vs.getNewVar();

    LABoundStore bs(vs);

    LABoundStore::BoundInfo x_nostrict_1 = bs.allocBoundPair(x, { Delta(1), Delta(1,1) }); // x <= 1 and x > 1
    LABoundStore::BoundInfo y_strict_0   = bs.allocBoundPair(y, { Delta(0, -1), Delta(0) }); // y < 0 and y >= 0

    LABoundStore::BoundInfo x_strict_m5   = bs.allocBoundPair(x, { Delta(-5, -1), Delta(-5) }); // x < -5 and x >= -5

    LABoundStore::BoundInfo y_minus_x_strict_0    = bs.allocBoundPair(y_minus_x, { Delta(0, -1), Delta(0) });    // y - x < 0 and y - x >= 0
    LABoundStore::BoundInfo y_minus_x_nostrict_0  = bs.allocBoundPair(y_minus_x, { Delta(0), Delta(0,1) });   // y - x <= 0 and y - x > 0

    bs.buildBounds();

    Simplex s(bs);

    s.newNonbasicVar(x);
    s.newNonbasicVar(y);
    auto p_y_plus_x = std::make_unique<PolynomialT<LVRef>>();
    p_y_plus_x->addTerm(x, 1);
    p_y_plus_x->addTerm(y, 1);
    s.newRow(y_minus_x, std::move(p_y_plus_x));

    s.initModel();
    s.assertBound(x_nostrict_1.ub);
    s.assertBound(x_strict_m5.lb);
    s.assertBound(y_strict_0.ub);
    s.assertBound(y_minus_x_strict_0.lb);
    s.assertBound(y_minus_x_nostrict_0.ub);

    Simplex::Explanation ex = s.checkSimplex();
    ASSERT_EQ(ex.size(), 0);
    ASSERT_LT(s.getValuation(y), (Delta{0,0}));
    ASSERT_LE(s.getValuation(x), (Delta{1,0}));
    ASSERT_GE(s.getValuation(x), (Delta{-5,0}));
    ASSERT_EQ(s.getValuation(x), -1 * s.getValuation(y));
    Real d = s.computeDelta();
    Real x_val = s.getValuation(x).R() + s.getValuation(x).D() * d;
    Real y_val = s.getValuation(y).R() + s.getValuation(y).D() * d;
    EXPECT_LT(y_val, 0);
    EXPECT_LE(x_val, 1);
    EXPECT_GE(x_val, -5);
    EXPECT_EQ(x_val, -1 * y_val);
}

}
