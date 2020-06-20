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

#define leq logic.mkNumLeq
#define geq logic.mkNumGeq
#define con logic.mkConst
#define min logic.mkNumMinus
#define zero logic.getTerm_NumZero()
#define var logic.mkNumVar
#define da solver.declareAtom
#define al solver.assertLit
#define pu solver.pushBacktrackPoint
#define po solver.popBacktrackPoint
#define chck res = solver.check(false)
TEST_F(STPSolverTest, test_Queens3_1) {
    auto s11 = var("s11");
    auto s12 = var("s12");
    auto s21 = var("s21");
    auto s22 = var("s22");
    auto r = var("ref");

    auto v1 = geq(min(s11, s21), con(3));
    auto v0 = geq(min(s21, s11), con(3));
    auto v3 = geq(min(s12, s22), con(3));
    auto v2 = geq(min(s22, s12), con(3));

    auto l0 = geq(min(s12, s11), con(3));
    auto l1 = geq(min(s22, s21), con(3));
    auto l2 = leq(min(s12, r), con(6));
    auto l3 = leq(min(s22, r), con(6));
    auto l4 = geq(min(s11, r), zero);
    auto l5 = geq(min(s21, r), zero);

    vec<DedElem> tmp;
    STPSolver solver(config, logic, tmp);
    da(v0);
    da(v1);
    da(v2);
    da(v3);
    da(l0);
    da(l1);
    da(l2);
    da(l3);
    da(l4);
    da(l5);

    pu();
    al(PtAsgn(l0, l_True));
    pu();
    al(PtAsgn(l1, l_True));
    pu();
    al(PtAsgn(l2, l_True));
    pu();
    al(PtAsgn(l3, l_True));
    pu();
    al(PtAsgn(l4, l_True));
    pu();
    al(PtAsgn(l5, l_True));

    TRes res;
    chck;
    ASSERT_EQ(res, TRes::SAT);

    pu();
    al(PtAsgn(v0, l_True));
    al(PtAsgn(v2, l_True));
    chck;
    ASSERT_EQ(res, TRes::SAT);


}

