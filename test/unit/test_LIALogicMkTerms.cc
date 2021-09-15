//
// Created by prova on 11.09.20.
//

#include <gtest/gtest.h>
#include <ArithLogic.h>

class LIALogicMkTermsTest: public ::testing::Test {
protected:
    LIALogicMkTermsTest() : logic(ArithLogic::ArithType::LIA) {}
    virtual void SetUp() {
        x = logic.mkIntVar("x");
        y = logic.mkIntVar("y");
        z = logic.mkIntVar("z");
    }
    ArithLogic logic;
    PTRef x;
    PTRef y;
    PTRef z;
};

TEST_F(LIALogicMkTermsTest, testIsNumTerm) {
    PTRef c = logic.mkBoolVar("c");
    ASSERT_FALSE(logic.isNumTerm(c));
    PTRef t = logic.mkNumVar("t");
    ASSERT_TRUE(logic.isNumTerm(t));
    PTRef e = logic.mkNumTimes({logic.mkNumVar("e"), logic.mkConst(-114)});
    ASSERT_TRUE(logic.isNumTerm(e));
    PTRef ite = logic.mkIte(c, t, e);
    ASSERT_TRUE(logic.isNumTerm(ite));
    PTRef ite_term = logic.mkNumTimes({ite, logic.mkConst(14)});
    ASSERT_TRUE(logic.isNumTerm(ite_term));

    PTRef sum = logic.mkNumPlus({t, e});
    ASSERT_FALSE(logic.isNumTerm(sum));
}

TEST_F(LIALogicMkTermsTest, testDeepLessThan) {
    PTRef a = logic.mkConst(3);
    PTRef b = logic.mkConst(-4);
    PTRef prod2 = logic.mkNumTimes({y, b});
    PTRef prod1 = logic.mkNumTimes({x, a});

    LessThan_deepPTRef lt_deep(&logic);
    ASSERT_EQ(lt_deep(prod1, prod2), lt_deep(x, y));
//    LessThan_PTRef lt_shallow;
//    ASSERT_NE(lt_shallow(prod1, prod2), lt_shallow(x, y));
}

TEST_F(LIALogicMkTermsTest, testDivMod) {
    PTRef two = logic.mkConst(2);
    PTRef div = logic.mkIntDiv(x,two);
    PTRef mod = logic.mkIntMod(x, two);
    EXPECT_EQ(logic.getSymRef(div), logic.get_sym_Int_DIV());
    EXPECT_EQ(logic.getSymRef(mod), logic.get_sym_Int_MOD());
}

TEST_F(LIALogicMkTermsTest, testMod_Plus) {
    PTRef two = logic.mkConst(2);
    PTRef mod = logic.mkIntMod(x,two);
    PTRef plus = logic.mkNumPlus({mod, two});
    EXPECT_EQ(logic.getSymRef(plus), logic.get_sym_Int_PLUS());
}

TEST_F(LIALogicMkTermsTest, testMod_Times) {
    PTRef two = logic.mkConst(2);
    PTRef three = logic.mkConst(3);
    PTRef mod = logic.mkIntMod(x,two);
    PTRef times = logic.mkNumTimes({mod, three});
    EXPECT_EQ(logic.getSymRef(times), logic.get_sym_Int_TIMES());
}

TEST_F(LIALogicMkTermsTest, testMod_Leq) {
    PTRef two = logic.mkConst(2);
    PTRef three = logic.mkConst(3);
    PTRef mod = logic.mkIntMod(x,two);
    PTRef leq = logic.mkNumLeq(mod, three);
    EXPECT_EQ(logic.getSymRef(leq), logic.get_sym_Num_LEQ());
}

TEST_F(LIALogicMkTermsTest, testDiv_Constants_PosPos) {
    PTRef two = logic.mkConst(2);
    PTRef three = logic.mkConst(3);
    PTRef div = logic.mkIntDiv(two, three);
    PTRef mod = logic.mkIntMod(two, three);
    EXPECT_EQ(div, logic.getTerm_NumZero());
    EXPECT_EQ(mod, two);
}

TEST_F(LIALogicMkTermsTest, testDiv_Constants_PosNeg) {
    PTRef two = logic.mkConst(2);
    PTRef mthree = logic.mkConst(-3);
    PTRef div = logic.mkIntDiv(two, mthree);
    PTRef mod = logic.mkIntMod(two, mthree);
    EXPECT_EQ(div, logic.getTerm_NumZero());
    EXPECT_EQ(mod, two);
}

TEST_F(LIALogicMkTermsTest, testDiv_Constants_NegPos) {
    PTRef mtwo = logic.mkConst(-2);
    PTRef three = logic.mkConst(3);
    PTRef div = logic.mkIntDiv(mtwo, three);
    PTRef mod = logic.mkIntMod(mtwo, three);
    EXPECT_EQ(div, logic.mkConst(-1));
    EXPECT_EQ(mod, logic.getTerm_NumOne());
}


TEST_F(LIALogicMkTermsTest, testDiv_Constants_NegNeg) {
    PTRef mtwo = logic.mkConst(-2);
    PTRef mthree = logic.mkConst(-3);
    PTRef div = logic.mkIntDiv(mtwo, mthree);
    PTRef mod = logic.mkIntMod(mtwo, mthree);
    EXPECT_EQ(div, logic.getTerm_NumOne());
    EXPECT_EQ(mod, logic.getTerm_NumOne());
}

TEST_F(LIALogicMkTermsTest, test_Inequality_Simplification)
{
    PTRef two = logic.mkConst("2");
    ASSERT_EQ(
            logic.mkNumLeq(logic.mkNumPlus({x,y}), z),
            logic.mkNumLeq(
                    logic.mkNumPlus({logic.mkNumTimes({x, two}), logic.mkNumTimes({y, two})}),
                    logic.mkNumTimes({z, two})
            )
    );
}

TEST_F(LIALogicMkTermsTest, test_EqualityNormalization) {
    PTRef two = logic.mkConst(2);
    PTRef eq1 = logic.mkEq(x, y);
    PTRef eq2 = logic.mkEq(logic.mkNumTimes(x, two), logic.mkNumTimes(y, two));
//    std::cout << logic.printTerm(eq1) << std::endl;
//    std::cout << logic.printTerm(eq2) << std::endl;
    EXPECT_EQ(eq1, eq2);
}

TEST_F(LIALogicMkTermsTest, test_EqualityNormalization_ToConstantExpression) {
    PTRef two = logic.mkConst(2);
    PTRef eq1 = logic.mkEq(x, logic.mkNumPlus(x, two));
    EXPECT_EQ(eq1, logic.getTerm_false());
    PTRef eq2 = logic.mkEq(logic.mkNumTimes(x, two), logic.getTerm_NumOne());
    EXPECT_EQ(eq2, logic.getTerm_false());
}

TEST_F(LIALogicMkTermsTest, test_EqualityNormalization_AlreadyNormalized) {
    PTRef two = logic.mkConst(2);
    PTRef three = logic.mkConst(3);
    PTRef eq1 = logic.mkEq(logic.mkNumPlus(logic.mkNumTimes(x, two), logic.mkNumTimes(y, three)), logic.getTerm_NumOne());
    ASSERT_NE(eq1, logic.getTerm_false());
    EXPECT_EQ(logic.getSymRef(eq1), logic.get_sym_Num_EQ());
}
