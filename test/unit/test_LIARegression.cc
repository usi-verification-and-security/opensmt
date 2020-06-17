//
// Created by Martin Blicha on 17.06.20.
//

#include <gtest/gtest.h>
#include <Opensmt.h>

class LIARegression: public ::testing::Test {
public:
    std::unique_ptr<Opensmt> getLIAOsmt() {
        return std::unique_ptr<Opensmt>(new Opensmt(opensmt_logic::qf_lia, "test"));
    }
};

TEST_F(LIARegression, test_LIAsubstitution) {
    auto const osmt = getLIAOsmt();
    auto & mainSolver = osmt->getMainSolver();
    auto & lialogic = osmt->getLIALogic();
    PTRef x = lialogic.mkNumVar("x");
    PTRef y = lialogic.mkNumVar("y");
    PTRef two = lialogic.mkConst(2);
    PTRef eq = lialogic.mkEq(x, lialogic.mkNumTimes(two, y));
    PTRef a = lialogic.mkBoolVar("a");
    PTRef conj = lialogic.mkAnd(
            lialogic.mkImpl(a, lialogic.mkEq(x, lialogic.getTerm_NumOne())),
            lialogic.mkImpl(lialogic.mkNot(a), lialogic.mkEq(x, lialogic.getTerm_NumOne()))
            );
    PTRef fla = lialogic.mkAnd(conj, eq);
    // x = 2y  AND (a => y=1) AND (~a => y=1)
    char* msg;
    mainSolver.insertFormula(fla, &msg);
    auto res = mainSolver.check();
//    if (res == s_True) {
//        auto model = mainSolver.getModel();
//        std::cout << lialogic.printTerm(model->evaluate(x)) << '\n';
//        std::cout << lialogic.printTerm(model->evaluate(y)) << std::endl;
//    }
    ASSERT_EQ(res, s_False);
}
