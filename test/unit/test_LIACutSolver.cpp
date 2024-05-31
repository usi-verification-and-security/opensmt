#include <gtest/gtest.h>
#include <Real.h>
#include <SMTConfig.h>
#include <lasolver/Simplex.h>

using Polynomial = PolynomialT<LVRef>;

TEST(LIACutSolver_test, test_computeEqualityBasis)
{

    SMTConfig c;
    LAVarStore vs;


    //our system
    //y >= x + 0.5
    //y >= -10x + 20
    //y <= x - 5

    LVRef x = vs.getNewVar();
    LVRef y = vs.getNewVar();

    //y - x
    LVRef y_minus_x = vs.getNewVar();
    auto p_y_minus_x = std::make_unique<Polynomial>();

    p_y_minus_x->addTerm(x, -1);
    p_y_minus_x->addTerm(y, 1);

    //-y - 10x
    LVRef minus_y_minus_ten_x = vs.getNewVar();
    auto p_minus_y_minus_ten_x = std::make_unique<Polynomial>();

    p_minus_y_minus_ten_x->addTerm(x, -10);
    p_minus_y_minus_ten_x->addTerm(y, -1);

    //2x - 2y
    LVRef two_x_minus_two_y = vs.getNewVar();
    auto p_two_x_minus_two_y = std::make_unique<Polynomial>();

    p_two_x_minus_two_y->addTerm(y, -2);
    p_two_x_minus_two_y->addTerm(x, 2);

    LABoundStore bs(vs);

    //LABoundStore::BoundInfo y_minus_x_nostrict_m5 = bs.allocBoundPair(y_minus_x, -5, false);  // y - x + 5 <= 0
    //LABoundStore::BoundInfo two_x_minus_two_y_nostrict_m1 = bs.allocBoundPair(two_x_minus_two_y, -1, false);    // 2x - 2y + 1 <= 0
    //LABoundStore::BoundInfo minus_y_minus_ten_x_nostrict_m20  = bs.allocBoundPair(minus_y_minus_ten_x, -20, false);   // -y - 10x + 20 <= 0

    bs.buildBounds();

    //Simplex s(c, m, bs);
    auto s = std::make_unique<Simplex>(bs);

    s->newNonbasicVar(x);
    s->newNonbasicVar(y);
    s->newRow(y_minus_x, std::move(p_y_minus_x));
    s->newRow(two_x_minus_two_y, std::move(p_two_x_minus_two_y));
    s->newRow(minus_y_minus_ten_x, std::move(p_minus_y_minus_ten_x));

    Simplex::Explanation explanation = s->checkSimplex();
    ASSERT_EQ(explanation.size(), 0); //this property has to be failed as the system is UNSAT then explanation size has to be >0
}
