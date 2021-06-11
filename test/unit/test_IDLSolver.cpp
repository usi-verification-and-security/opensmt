//
// Created by Martin Blicha on 12.12.19.
//

#include <gtest/gtest.h>
#include <SMTConfig.h>
#include <LIALogic.h>
#include <IDLSolver.h>

class IDLSolverTest : public ::testing::Test {
protected:
    IDLSolverTest() {}
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




TEST_F(IDLSolverTest, test_SimpleTest){
    PTRef ineq1 = logic.mkNumLeq(logic.mkNumMinus(x, y), logic.getTerm_NumZero());
    PTRef ineq2 = logic.mkNumLeq(logic.mkNumMinus(y, z), logic.getTerm_NumZero());
    PTRef ineq3 = logic.mkNumLeq(logic.mkNumMinus(z, x), logic.mkConst(-1));
    PTRef ineq4 = logic.mkNumLeq(logic.mkConst(3), x);
    PTRef ineq5 = logic.mkNumLeq(y, logic.mkConst(-2));

    IDLSolver solver(config, logic);

    solver.declareAtom(ineq1);
    solver.declareAtom(ineq2);
    solver.declareAtom(ineq3);
    solver.declareAtom(ineq4);
    solver.declareAtom(ineq5);

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
    //vec<PtAsgn> v{};
    //solver.getConflict(true, v);
    //ASSERT_TRUE(v[0] == PtAsgn(ineq1, l_True) && v[1] == PtAsgn(ineq2, l_True)
    //             || v[0] == PtAsgn(ineq2, l_True) && v[1] == PtAsgn(ineq1, l_True));

    solver.popBacktrackPoints(1);

    solver.assertLit(PtAsgn(ineq3, l_False));
    res = solver.check(true);
    ASSERT_EQ(res, TRes::SAT);
/**/
    solver.pushBacktrackPoint();
    solver.assertLit(PtAsgn(ineq4, l_True));
    res = solver.check(true);
    ASSERT_EQ(res, TRes::SAT);

    solver.pushBacktrackPoint();
    solver.assertLit(PtAsgn(ineq5, l_True));
    res = solver.check(true);
    ASSERT_EQ(res, TRes::UNSAT);

    solver.popBacktrackPoints(1);

    solver.assertLit(PtAsgn(ineq5, l_False));
    res = solver.check(true);
    ASSERT_EQ(res, TRes::SAT);
/**/
    solver.computeModel();
    ModelBuilder builder(logic);
    solver.fillTheoryFunctions(builder);
    auto model = builder.build();
    auto valX = model->evaluate(x);
    auto valY = model->evaluate(y);
    auto valZ = model->evaluate(z);
    ASSERT_NE(valX, PTRef_Undef);
    ASSERT_NE(valY, PTRef_Undef);
    ASSERT_NE(valZ, PTRef_Undef);

    ptrdiff_t numX, numY, numZ;
    std::stringstream ss(logic.pp(valX));
    ss >> numX;
    std::stringstream ss2(logic.pp(valY));
    ss2 >> numY;
    std::stringstream ss3(logic.pp(valZ));
    ss3 >> numZ;



    ASSERT_LE(numX - numY, 0);
    ASSERT_LE(numY - numZ, 0);
    ASSERT_GT(numZ - numX, -1);
    ASSERT_LE(3, numX);
    ASSERT_GT(numY, -2);
}

class SafeIntTest : public ::testing::Test {};

TEST_F(SafeIntTest, test_add_pass){
    SafeInt a(PTRDIFF_MAX - 1), b(1);
    SafeInt c(PTRDIFF_MIN + 1), d(-1);
    SafeInt e{};
    ASSERT_NO_THROW(e = a + b);
    ASSERT_NO_THROW(e = c + d);
}

TEST_F(SafeIntTest, test_add_fail_over){
    SafeInt a(PTRDIFF_MAX-2);
    SafeInt b(3);
    ASSERT_ANY_THROW(a+b);

}

TEST_F(SafeIntTest, test_add_fail_under){
   SafeInt a(PTRDIFF_MIN + 100), b(-200);
   ASSERT_ANY_THROW(a+b);
}

TEST_F(SafeIntTest, test_sub_pass){
    SafeInt a(PTRDIFF_MAX - 10);
    ASSERT_NO_THROW(a -= SafeInt(-10));
    SafeInt b(PTRDIFF_MIN + 5);
    ASSERT_NO_THROW(b -= SafeInt(5));
}

TEST_F(SafeIntTest, test_sub_fail_under){
    SafeInt a(PTRDIFF_MIN + 100);
    ASSERT_ANY_THROW(a -= SafeInt(101));
}

TEST_F(SafeIntTest, test_sub_fail_over){
    SafeInt a(PTRDIFF_MAX - 42);
    ASSERT_ANY_THROW(a -= SafeInt(-43));
}


