//
// Created by Antti on 04.08.20.
//
#include <gtest/gtest.h>
#include <Logic.h>
#include <ArithLogic.h>
#include <IteToSwitch.h>
#include <IteHandler.h>
#include <TreeOps.h>

class LogicIteTest: public ::testing::Test {
public:
    Logic logic;
    LogicIteTest() : logic{} {}
};

class LRAIteTest: public ::testing::Test {
public:
    ArithLogic logic;
    LRAIteTest() : logic{ArithLogic::ArithType::LRA} {}
};

class IteManagerTest: public ::testing::Test {
public:
    class IteToSwitchInternal: public IteToSwitch  {
    public:
        const vec<PTRef> & getTopLevelItes() const { return iteDag.getTopLevelItes(); }
        IteToSwitchInternal(Logic &l, PTRef tr) : IteToSwitch(l, tr) {}
    };
    ArithLogic logic;
    SRef lrasort;

    IteManagerTest() : logic{ArithLogic::ArithType::LRA}, lrasort(logic.getSort_num()) {}

    void printTopLevelSwitches(IteToSwitch &iteManager) {
        PTRef tr = logic.getTerm_true();
        tr = iteManager.conjoin(tr);
        std::cout << logic.pp(tr) << endl;
    }
    static bool contains(const vec<PTRef>& trs, PTRef tr) {
        return std::any_of(trs.begin(), trs.end(), [tr](PTRef tr_in_vec) { return tr_in_vec == tr; });
    }
};

TEST_F(LogicIteTest, test_UFIte) {
    SRef ufsort = logic.declareSort("U");

    PTRef x = logic.mkVar(ufsort, "x");
    PTRef y = logic.mkVar(ufsort, "y");
    PTRef cond = logic.mkEq(x, y);

    PTRef ite = logic.mkIte(cond, x, y);
    ASSERT_TRUE(logic.isIte(ite));
    std::cout << logic.pp(ite) << endl;

    ite = logic.mkIte(logic.getTerm_true(), x, y);
    ASSERT_EQ(ite, x);

    ite = logic.mkIte(logic.getTerm_false(), x, y);
    ASSERT_EQ(ite, y);

}

TEST_F(LogicIteTest, test_BoolIte) {
    SRef boolsort = logic.getSort_bool();

    PTRef x = logic.mkVar(boolsort, "x");
    PTRef y = logic.mkVar(boolsort, "y");
    PTRef cond = logic.mkEq(x, y);

    PTRef ite = logic.mkIte(cond, x, y);
    ASSERT_TRUE(logic.isIte(ite));
    std::cout << logic.pp(ite) << endl;
}

TEST_F(LRAIteTest, test_LRAIte) {
    SRef lrasort = logic.getSort_num();

    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef cond = logic.mkEq(x, y);

    PTRef ite = logic.mkIte(cond, x, y);
    ASSERT_TRUE(logic.isIte(ite));
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
    PTRef ites = iteManager.conjoin(logic.getTerm_true());

    ASSERT_TRUE(logic.isAnd(ites));
    Pterm& and_term = logic.getPterm(ites);
    ASSERT_TRUE(logic.isOr(and_term[0]));
    ASSERT_TRUE(logic.isOr(and_term[1]));
    Pterm& or_term_0 = logic.getPterm(and_term[0]);
    Pterm& or_term_1 = logic.getPterm(and_term[1]);
    ASSERT_TRUE(or_term_0[0] == cond || or_term_1[0] == cond || or_term_0[0] == logic.mkNot(cond) || or_term_1[0] == logic.mkNot(cond));

    std::cout << logic.pp(ites) << std::endl;
    printTopLevelSwitches(iteManager);

}

TEST_F(IteManagerTest, test_IteTimesConst) {

    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef cond = logic.mkEq(x, y);
    PTRef c1 = logic.mkConst("1");
    PTRef c2 = logic.mkConst("2");
    PTRef ite = logic.mkIte(cond, c1, c2);
    EXPECT_NO_THROW(logic.mkRealTimes(ite, c2));
}

TEST_F(IteManagerTest, test_IteTimesVar) {

    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef cond = logic.mkEq(x, y);
    PTRef c1 = logic.mkConst("1");
    PTRef c2 = logic.mkConst("2");
    PTRef ite = logic.mkIte(cond, c1, c2);

    EXPECT_THROW(logic.mkRealTimes(ite, x), LANonLinearException);

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

    EXPECT_THROW(logic.mkRealTimes(ite1, ite2), LANonLinearException);
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
    IteToSwitchInternal iteManager(logic, eq);
    const vec<PTRef> & ites = iteManager.getTopLevelItes();
    ASSERT_TRUE(contains(ites, ite2));
    ASSERT_FALSE(contains(ites, ite1));

    printTopLevelSwitches(iteManager);
}

TEST_F(IteManagerTest, test_IteSum) {
    PTRef x = logic.mkVar(lrasort, "x");
    PTRef y = logic.mkVar(lrasort, "y");
    PTRef cond = logic.mkEq(x, y);
    PTRef c1 = logic.mkConst("1");
    PTRef c2 = logic.mkConst("2");
    PTRef ite = logic.mkIte(cond, c1, c2);
    EXPECT_NO_THROW(logic.mkRealPlus(ite, c2));
}

TEST_F(IteManagerTest, testBoolean) {
    PTRef c = logic.mkBoolVar("c");
    PTRef a = logic.mkBoolVar("a");
    //  (ite c (and (ite c a (not a)) (not c)) (and a c)))
    PTRef ite1 = logic.mkIte(c, a, logic.mkNot(a));
    PTRef and_tr = logic.mkAnd(ite1, logic.mkNot(c));
    PTRef ite2 = logic.mkIte(c, and_tr, logic.mkAnd(a, c));
    IteToSwitchInternal iteToSwitch(logic, ite2);
    ASSERT_TRUE(contains(iteToSwitch.getTopLevelItes(), ite1));
    ASSERT_TRUE(contains(iteToSwitch.getTopLevelItes(), ite2));

    PTRef tr = iteToSwitch.conjoin(logic.getTerm_true());
    std::cout << logic.pp(tr) << std::endl << std::endl;
    std::cout << logic.pp(ite2) << std::endl;
}

TEST_F(LogicIteTest, test_IteHandlerNestedIte) {
    //  (ite b (ite c a (not a)) d)
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef d = logic.mkBoolVar("d");
    PTRef inner = logic.mkIte(c, a, logic.mkNot(a));
    PTRef outer = logic.mkIte(b, inner, d);
    IteHandler handler(logic);
    PTRef res = handler.rewrite(outer);
    std::cout << logic.pp(res) << std::endl;
    // only 1 variable should be introduced for the single top-level ITE
    auto atoms = getAtoms(res, logic);
    ASSERT_EQ(atoms.size(), 5); // 4 original + 1 auxiliary variable
}

TEST_F(LogicIteTest, test_IteHandlerNestedAndTopLevelAtTheSameTime) {
    //  (and (ite b (ite c a (not a)) d) (or d (ite c a (not a)))
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef d = logic.mkBoolVar("d");
    PTRef inner = logic.mkIte(c, a, logic.mkNot(a));
    PTRef outer = logic.mkIte(b, inner, d);
    PTRef part2 = logic.mkOr(d, inner);
    PTRef fla = logic.mkAnd(outer, part2);
    IteHandler handler(logic);
    PTRef res = handler.rewrite(fla);
    std::cout << logic.pp(res) << std::endl;
    // 2 variables should be introduced since the ITE that is nested in the first part is top-level in the second part of the formula
    auto atoms = getAtoms(res, logic);
    ASSERT_EQ(atoms.size(), 6); // 4 original + 2 auxiliary variables
}

TEST_F(LogicIteTest, test_IteHandler_RewriteTwiceSame) {
    //  (ite b (ite c a (not a)) d)
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef d = logic.mkBoolVar("d");
    PTRef inner = logic.mkIte(c, a, logic.mkNot(a));
    PTRef fla = logic.mkIte(b, inner, d);

    PTRef res1 = IteHandler(logic).rewrite(fla);
    PTRef res2 = IteHandler(logic).rewrite(fla);
    ASSERT_EQ(res1, res2);
}

TEST_F(LogicIteTest, test_IteHandler_RewriteTwiceDifferent) {
    //  (ite b (ite c a (not a)) d)
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef d = logic.mkBoolVar("d");
    PTRef inner = logic.mkIte(c, a, logic.mkNot(a));
    PTRef fla = logic.mkIte(b, inner, d);
    PTRef res1 = IteHandler(logic, 0).rewrite(fla);
    PTRef res2 = IteHandler(logic, 1).rewrite(fla);
    ASSERT_NE(res1, res2);
}