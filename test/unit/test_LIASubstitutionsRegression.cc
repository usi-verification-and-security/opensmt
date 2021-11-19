//
// Created by Martin Blicha on 17.06.20.
//

#include <gtest/gtest.h>
#include <Opensmt.h>

class LIASubstitutionsRegression: public ::testing::Test {
public:
    std::unique_ptr<Opensmt> getLIAOsmt() {
        return std::make_unique<Opensmt>(opensmt_logic::qf_lia, "test");
    }
};

TEST_F(LIASubstitutionsRegression, test_LIAsubstitution) {
    auto const osmt = getLIAOsmt();
    auto & mainSolver = osmt->getMainSolver();
    auto & lialogic = osmt->getLIALogic();
    PTRef x = lialogic.mkIntVar("x");
    PTRef y = lialogic.mkIntVar("y");
    PTRef two = lialogic.mkIntConst(2);
    PTRef eq = lialogic.mkEq(x, lialogic.mkTimes(two, y));
    PTRef a = lialogic.mkBoolVar("a");
    PTRef conj = lialogic.mkAnd(
            lialogic.mkImpl(a, lialogic.mkEq(x, lialogic.getTerm_IntOne())),
            lialogic.mkImpl(lialogic.mkNot(a), lialogic.mkEq(x, lialogic.getTerm_IntOne()))
            );
    PTRef fla = lialogic.mkAnd(conj, eq);
    // x = 2y  AND (a => x=1) AND (~a => x=1)
    char* msg;
    mainSolver.insertFormula(fla, &msg);
    auto res = mainSolver.check();
    ASSERT_EQ(res, s_False);
}
