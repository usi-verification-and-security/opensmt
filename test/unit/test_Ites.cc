//
// Created by Antti on 04.08.20.
//
#include <gtest/gtest.h>
#include <Logic.h>
#include <LRALogic.h>
#include "../../src/itehandler/IteToSwitch.h"

class LogicIteTest: public ::testing::Test {
public:
    Logic logic;
    LogicIteTest() : logic{} {}
};

class LRAIteTest: public ::testing::Test {
public:
    LRALogic logic;
    LRAIteTest() : logic{} {}
};

class IteManagerTest: public ::testing::Test {
public:
    LRALogic logic;
    SRef lrasort;

    IteManagerTest() : lrasort(logic.getSort_num()) {}

    void printTopLevelSwitches(IteToSwitch &iteManager) {
        PTRef tr = logic.getTerm_true();
        tr = iteManager.conjoin(tr);
        std::cout << logic.pp(tr) << endl;
    }
};

TEST_F(LogicIteTest, test_UFIte) {
    SRef ufsort = logic.declareSort("U", nullptr);

    PTRef x = logic.mkVar(ufsort, "x");
    PTRef y = logic.mkVar(ufsort, "y");
    PTRef cond = logic.mkEq(x, y);

    vec<PTRef> args;
    args.push(cond);
    args.push(x);
    args.push(y);
    PTRef ite = logic.mkIte(args);
    std::cout << logic.pp(ite) << endl;

    args.clear();
    args.push(logic.getTerm_true());
    args.push(x);
    args.push(y);
    ite = logic.mkIte(args);
    ASSERT_EQ(ite, x);

    args.clear();
    args.push(logic.getTerm_false());
    args.push(x);
    args.push(y);
    ite = logic.mkIte(args);
    ASSERT_EQ(ite, y);

}

TEST_F(LogicIteTest, test_BoolIte) {
    SRef boolsort = logic.getSort_bool();

    PTRef x = logic.mkVar(boolsort, "x");
    PTRef y = logic.mkVar(boolsort, "y");
    PTRef cond = logic.mkEq(x, y);

    vec<PTRef> args;
    args.push(cond);
    args.push(x);
    args.push(y);
    PTRef ite = logic.mkIte(args);
    std::cout << logic.pp(ite) << endl;
}

TEST_F(LRAIteTest, test_LRAIte) {
    SRef lrasort = logic.getSort_num();

    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef cond = logic.mkEq(x, y);

    vec<PTRef> args;
    args.push(cond);
    args.push(x);
    args.push(y);
    PTRef ite = logic.mkIte(args);
    std::cout << logic.pp(ite) << endl;
}

TEST_F(IteManagerTest, test_Basic) {

    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef cond = logic.mkEq(x, y);

    PTRef ite = logic.mkIte(cond, x, y);
    SRef sr = logic.getSortRef(ite);
    ASSERT_EQ(sr, logic.getSort_num());
    PTRef eq = logic.mkEq(x, ite);

    IteToSwitch iteManager(logic, eq);
    printTopLevelSwitches(iteManager);

}

TEST_F(IteManagerTest, test_IteTimesConst) {

    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef cond = logic.mkEq(x, y);
    PTRef c1 = logic.mkConst("1");
    PTRef c2 = logic.mkConst("2");
    PTRef ite = logic.mkIte(cond, c1, c2);
    PTRef prod = logic.mkNumTimes(ite, c2);
    PTRef eq = logic.mkEq(x, prod);
    IteToSwitch iteManager(logic, eq);
    printTopLevelSwitches(iteManager);
}

TEST_F(IteManagerTest, test_IteTimesVar) {

    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef cond = logic.mkEq(x, y);
    PTRef c1 = logic.mkConst("1");
    PTRef c2 = logic.mkConst("2");
    PTRef ite = logic.mkIte(cond, c1, c2);

    try {
        logic.mkNumTimes(ite, x);
    } catch (LANonLinearException) {
        return;
    }
    ASSERT_FALSE(true);
}

TEST_F(IteManagerTest, test_IteTimesIte) {

    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef z = logic.mkVar(lrasort, "z");
    PTRef cond1 = logic.mkEq(x, y);
    PTRef c1 = logic.mkConst("1");
    PTRef c2 = logic.mkConst("2");
    PTRef ite1 = logic.mkIte(cond1, c1, c2);

    PTRef cond2 = logic.mkEq(x, z);
    PTRef ite2 = logic.mkIte(cond2, c2, c1);

    try {
        logic.mkNumTimes(ite1, ite2);
    } catch (LANonLinearException) {
        return;
    }
    ASSERT_FALSE(true);
}

TEST_F(IteManagerTest, test_IteChain) {
    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef z = logic.mkVar(lrasort, "z");
    PTRef cond1 = logic.mkEq(x, y);
    PTRef c1 = logic.mkConst("1");
    PTRef c2 = logic.mkConst("2");
    PTRef ite1 = logic.mkIte(cond1, c1, c2);

    PTRef cond2 = logic.mkEq(x, z);
    PTRef ite2 = logic.mkIte(cond2, ite1, c1);
    PTRef eq = logic.mkEq(x, ite2);
    IteToSwitch iteManager(logic, eq);
    printTopLevelSwitches(iteManager);
}

TEST_F(IteManagerTest, test_IteSum) {
    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef cond = logic.mkEq(x, y);
    PTRef c1 = logic.mkConst("1");
    PTRef c2 = logic.mkConst("2");
    PTRef ite = logic.mkIte(cond, c1, c2);
    PTRef sum = logic.mkNumPlus(ite, c2);
    logic.mkEq(x, sum);
}