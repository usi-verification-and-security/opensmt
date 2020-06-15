//
// Created by Martin Blicha on 12.12.19.
//

#include <gtest/gtest.h>
#include <SMTConfig.h>
#include <LIALogic.h>
#include <STPSolver.h>

class STPSolverTest : public ::testing::Test {
protected:
    STPSolverTest(): logic{config} {}
    virtual void SetUp() {
        x = logic.mkNumVar("x");
        y = logic.mkNumVar("y");
        z = logic.mkNumVar("z");
    }
    SMTConfig config;
    LIALogic logic;
    SRef ufsort;
    PTRef x;
    PTRef y;
    PTRef z;
};


TEST_F(STPSolverTest, test_SimpleTest){
    PTRef ineq1 = logic.mkNumLeq(logic.mkNumMinus(x, y), logic.getTerm_NumZero());
    PTRef ineq2 = logic.mkNumLeq(logic.mkNumMinus(y, z), logic.getTerm_NumZero());
    PTRef ineq3 = logic.mkNumLeq(logic.mkNumMinus(z, x), logic.mkConst(-1));

    STPSolver solver(config, logic);

    solver.declareAtom(ineq1);
    solver.declareAtom(ineq2);
    solver.declareAtom(ineq3);

    solver.pushBacktrackPoint();
    solver.assertLit(PtAsgn(ineq1, l_True));
    TRes res = solver.check(true);
    ASSERT_EQ(res, TRes::SAT);

    solver.pushBacktrackPoint();
    solver.assertLit(PtAsgn(ineq2, l_True));
    res = solver.check(true);
    ASSERT_EQ(res, TRes::SAT);

    solver.pushBacktrackPoint();
    solver.assertLit(PtAsgn(ineq3, l_True));
    res = solver.check(true);
    ASSERT_EQ(res, TRes::UNSAT);
    vec<PtAsgn> v{};
    solver.getConflict(true, v);
    ASSERT_TRUE(v[0] == PtAsgn(ineq1, l_True) && v[1] == PtAsgn(ineq2, l_True)
                 || v[0] == PtAsgn(ineq2, l_True) && v[1] == PtAsgn(ineq1, l_True));

    solver.popBacktrackPoints(1);

    solver.assertLit(PtAsgn(ineq3, l_False));
    res = solver.check(true);
    ASSERT_EQ(res, TRes::SAT);
}

