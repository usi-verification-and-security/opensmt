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
