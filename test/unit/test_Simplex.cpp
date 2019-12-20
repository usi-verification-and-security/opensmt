//
// Created by prova on 08.10.19.
//

#include <gtest/gtest.h>
#include <lasolver/Simplex.h>
#include <SMTConfig.h>
#include <lasolver/LABounds.h>
#include <lasolver/LAVar.h>

TEST(Simplex_test, test_ops_in_Simplex)
{
    SMTConfig c;
    LAVarStore vs;

    LVRef x = vs.getNewVar();
    LVRef y = vs.getNewVar();

    LVRef y_minus_x = vs.getNewVar();
    auto p_y_minus_x = std::unique_ptr<Polynomial>(new Polynomial());

    p_y_minus_x->addTerm(x, -1);
    p_y_minus_x->addTerm(y, 1);

    LABoundStore bs(vs);

    LABoundStore::BoundInfo x_strict_0   = bs.allocBoundPair(x, 0, true); // x < 0 and x >= 0
    LABoundStore::BoundInfo x_nostrict_0 = bs.allocBoundPair(x, 0, false); // x <= 0 and x > 0
    LABoundStore::BoundInfo y_strict_0   = bs.allocBoundPair(y, 0, true); // y < 0 and y >= 0
    LABoundStore::BoundInfo y_nostrict_0 = bs.allocBoundPair(y, 0, false); // y <= 0 and y > 0

    LABoundStore::BoundInfo x_strict_1   = bs.allocBoundPair(x, 1, true); // x < 1 and x >= 1
    LABoundStore::BoundInfo x_nostrict_1 = bs.allocBoundPair(x, 1, false); // x <= 1 and x > 1
    LABoundStore::BoundInfo y_strict_1   = bs.allocBoundPair(y, 1, true); // y < 1 and y >= 1
    LABoundStore::BoundInfo y_nostrict_1 = bs.allocBoundPair(y, 1, false); // y <= 1 and y > 1

    LABoundStore::BoundInfo y_minus_x_strict_0    = bs.allocBoundPair(y_minus_x, 0, true);    // y - x < 0 and y - x >= 0
    LABoundStore::BoundInfo y_minus_x_nostrict_0  = bs.allocBoundPair(y_minus_x, 0, false);   // y - x <= 0 and y - x > 0
    LABoundStore::BoundInfo y_minus_x_strict_m1   = bs.allocBoundPair(y_minus_x, -1, true);   // y - x + 1 <  0
    LABoundStore::BoundInfo y_minus_x_nostrict_m1 = bs.allocBoundPair(y_minus_x, -1, false);  // y - x + 1 <= 0
    LABoundStore::BoundInfo y_minus_x_strict_1    = bs.allocBoundPair(y_minus_x, 1, true);    // y - x - 1 <  0
    LABoundStore::BoundInfo y_minus_x_nostrict_1  = bs.allocBoundPair(y_minus_x, 1, false);   // y - x - 1 <= 0

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
    cout << x_val.R() + x_val.D() * d << endl;
    Delta y_val = s.getValuation(y);
    cout << y_val.R() + y_val.D() * d << endl;
    Delta sum = s.getValuation(y_minus_x);
    cout << sum.R() + sum.D() * d << endl;

    s.assertBoundOnVar(x, x_strict_0.lb);
    s.assertBoundOnVar(y, y_strict_0.lb);

    s.pushBacktrackPoint();

    s.assertBoundOnVar(x, x_strict_1.ub);
    s.assertBoundOnVar(y, y_strict_1.ub);

    ex = s.checkSimplex();
    ASSERT_EQ(ex.size(), 0);
    d = s.computeDelta();
    x_val = s.getValuation(x);
    cout << x_val.R() + x_val.D() * d << endl;
    y_val = s.getValuation(y);
    cout << y_val.R() + y_val.D() * d << endl;
    sum = s.getValuation(y_minus_x);
    cout << sum.R() + sum.D() * d << endl;

    ex = s.assertBoundOnVar(y_minus_x, y_minus_x_nostrict_1.lb);
    ASSERT_EQ(ex.size(), 0); // not detectable at this point
    ex = s.checkSimplex();
    ASSERT_EQ(ex.size(), 3);

    s.popBacktrackPoint();

    ex = s.assertBoundOnVar(y_minus_x, y_minus_x_nostrict_0.lb);
    s.assertBoundOnVar(x, x_nostrict_1.lb);
    s.assertBoundOnVar(y, y_nostrict_1.lb);
    ex = s.checkSimplex();
    ASSERT_EQ(ex.size(), 0);
    d = s.computeDelta();
    x_val = s.getValuation(x);
    cout << "x = " << x_val.R() + x_val.D() * d << endl;
    y_val = s.getValuation(y);
    cout << "y = " << y_val.R() + y_val.D() * d << endl;
    sum = s.getValuation(y_minus_x);
    cout << "y - x = " << sum.R() + sum.D() * d << endl;
}

TEST(Simplex_test, test_Assignment)
{
    SMTConfig c;
    LAVarStore vs;

    LVRef x = vs.getNewVar();
    LVRef y = vs.getNewVar();

    LVRef y_minus_x = vs.getNewVar();

    LABoundStore bs(vs);

    LABoundStore::BoundInfo x_nostrict_1 = bs.allocBoundPair(x, 1, false); // x <= 1 and x > 0
    LABoundStore::BoundInfo y_strict_0   = bs.allocBoundPair(y, 0, true); // y < 0 and y >= 0

    LABoundStore::BoundInfo x_strict_m5   = bs.allocBoundPair(x, -5, true); // x < -5 and x >= -5

    LABoundStore::BoundInfo y_minus_x_strict_0    = bs.allocBoundPair(y_minus_x, 0, true);    // y - x < 0 and y - x >= 0
    LABoundStore::BoundInfo y_minus_x_nostrict_0  = bs.allocBoundPair(y_minus_x, 0, false);   // y - x <= 0 and y - x > 0

    bs.buildBounds();

    Simplex s(bs);

    s.newNonbasicVar(x);
    s.newNonbasicVar(y);
    auto p_y_plus_x = std::unique_ptr<Polynomial>(new Polynomial());
    p_y_plus_x->addTerm(x, 1);
    p_y_plus_x->addTerm(y, 1);
    s.newRow(y_minus_x, std::move(p_y_plus_x));

    s.initModel();
    s.assertBoundOnVar(x_nostrict_1.v, x_nostrict_1.ub);
    s.assertBoundOnVar(x_strict_m5.v, x_strict_m5.lb);
    s.assertBoundOnVar(y_strict_0.v, y_strict_0.ub);
    s.assertBoundOnVar(y_minus_x_strict_0.v, y_minus_x_strict_0.lb);
    s.assertBoundOnVar(y_minus_x_nostrict_0.v, y_minus_x_nostrict_0.ub);

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
