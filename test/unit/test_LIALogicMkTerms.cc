//
// Created by prova on 11.09.20.
//

#include <gtest/gtest.h>
#include <ArithLogic.h>
#include "DivModRewriter.h"
#include "IteHandler.h"
#include "TreeOps.h"

class LIALogicMkTermsTest: public ::testing::Test {
protected:
    LIALogicMkTermsTest() : logic(opensmt::Logic_t::QF_LIA) {}
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
    PTRef t = logic.mkIntVar("t");
    ASSERT_TRUE(logic.isNumTerm(t));
    PTRef e = logic.mkTimes(logic.mkIntVar("e"), logic.mkIntConst(-114));
    ASSERT_TRUE(logic.isNumTerm(e));
    PTRef ite = logic.mkIte(c, t, e);
    ASSERT_TRUE(logic.isNumTerm(ite));
    PTRef ite_term = logic.mkTimes(ite, logic.mkIntConst(14));
    ASSERT_TRUE(logic.isNumTerm(ite_term));

    PTRef sum = logic.mkPlus(t, e);
    ASSERT_FALSE(logic.isNumTerm(sum));
}

TEST_F(LIALogicMkTermsTest, testDeepLessThan) {
    PTRef a = logic.mkIntConst(3);
    PTRef b = logic.mkIntConst(-4);
    PTRef prod2 = logic.mkTimes(y, b);
    PTRef prod1 = logic.mkTimes(x, a);

    LessThan_deepPTRef lt_deep(logic);
    ASSERT_EQ(lt_deep(prod1, prod2), lt_deep(x, y));
//    LessThan_PTRef lt_shallow;
//    ASSERT_NE(lt_shallow(prod1, prod2), lt_shallow(x, y));
}

TEST_F(LIALogicMkTermsTest, testDivMod) {
    PTRef two = logic.mkIntConst(2);
    PTRef div = logic.mkIntDiv(x,two);
    PTRef mod = logic.mkMod(x, two);
    EXPECT_EQ(logic.getSymRef(div), logic.get_sym_Int_DIV());
    EXPECT_EQ(logic.getSymRef(mod), logic.get_sym_Int_MOD());
}

TEST_F(LIALogicMkTermsTest, testMod_Plus) {
    PTRef two = logic.mkIntConst(2);
    PTRef mod = logic.mkMod(x,two);
    PTRef plus = logic.mkPlus(mod, two);
    EXPECT_EQ(logic.getSymRef(plus), logic.get_sym_Int_PLUS());
}

TEST_F(LIALogicMkTermsTest, testMod_Times) {
    PTRef two = logic.mkIntConst(2);
    PTRef three = logic.mkIntConst(3);
    PTRef mod = logic.mkMod(x,two);
    PTRef times = logic.mkTimes(mod, three);
    EXPECT_EQ(logic.getSymRef(times), logic.get_sym_Int_TIMES());
}

TEST_F(LIALogicMkTermsTest, testMod_Leq) {
    PTRef two = logic.mkIntConst(2);
    PTRef three = logic.mkIntConst(3);
    PTRef mod = logic.mkMod(x,two);
    PTRef leq = logic.mkLeq(mod, three);
    EXPECT_EQ(logic.getSymRef(leq), logic.get_sym_Int_LEQ());
}

TEST_F(LIALogicMkTermsTest, testDiv_Constants_PosPos) {
    PTRef two = logic.mkIntConst(2);
    PTRef three = logic.mkIntConst(3);
    PTRef div = logic.mkIntDiv(two, three);
    PTRef mod = logic.mkMod(two, three);
    EXPECT_EQ(div, logic.getTerm_IntZero());
    EXPECT_EQ(mod, two);
}

TEST_F(LIALogicMkTermsTest, testDiv_Constants_PosNeg) {
    PTRef two = logic.mkIntConst(2);
    PTRef mthree = logic.mkIntConst(-3);
    PTRef div = logic.mkIntDiv(two, mthree);
    PTRef mod = logic.mkMod(two, mthree);
    EXPECT_EQ(div, logic.getTerm_IntZero());
    EXPECT_EQ(mod, two);
}

TEST_F(LIALogicMkTermsTest, testDiv_Constants_NegPos) {
    PTRef mtwo = logic.mkIntConst(-2);
    PTRef three = logic.mkIntConst(3);
    PTRef div = logic.mkIntDiv(mtwo, three);
    PTRef mod = logic.mkMod(mtwo, three);
    EXPECT_EQ(div, logic.mkIntConst(-1));
    EXPECT_EQ(mod, logic.getTerm_IntOne());
}


TEST_F(LIALogicMkTermsTest, testDiv_Constants_NegNeg) {
    PTRef mtwo = logic.mkIntConst(-2);
    PTRef mthree = logic.mkIntConst(-3);
    PTRef div = logic.mkIntDiv(mtwo, mthree);
    PTRef mod = logic.mkMod(mtwo, mthree);
    EXPECT_EQ(div, logic.getTerm_IntOne());
    EXPECT_EQ(mod, logic.getTerm_IntOne());
}

TEST_F(LIALogicMkTermsTest, test_Inequality_Simplification)
{
    PTRef two = logic.mkConst("2");
    ASSERT_EQ(
            logic.mkLeq(logic.mkPlus(x,y), z),
            logic.mkLeq(
                    logic.mkPlus(logic.mkTimes(x, two), logic.mkTimes(y, two)),
                    logic.mkTimes(z, two)
            )
    );
}

TEST_F(LIALogicMkTermsTest, test_EqualityNormalization) {
    PTRef two = logic.mkIntConst(2);
    PTRef eq1 = logic.mkEq(x, y);
    PTRef eq2 = logic.mkEq(logic.mkTimes(x, two), logic.mkTimes(y, two));
//    std::cout << logic.printTerm(eq1) << std::endl;
//    std::cout << logic.printTerm(eq2) << std::endl;
    EXPECT_EQ(eq1, eq2);
}

TEST_F(LIALogicMkTermsTest, test_EqualityNormalization_ToConstantExpression) {
    PTRef two = logic.mkIntConst(2);
    PTRef eq1 = logic.mkEq(x, logic.mkPlus(x, two));
    EXPECT_EQ(eq1, logic.getTerm_false());
    PTRef eq2 = logic.mkEq(logic.mkTimes(x, two), logic.getTerm_IntOne());
    EXPECT_EQ(eq2, logic.getTerm_false());
}

TEST_F(LIALogicMkTermsTest, test_EqualityNormalization_AlreadyNormalized) {
    PTRef two = logic.mkIntConst(2);
    PTRef three = logic.mkIntConst(3);
    PTRef eq1 = logic.mkEq(logic.mkPlus(logic.mkTimes(x, two), logic.mkTimes(y, three)), logic.getTerm_IntOne());
    ASSERT_NE(eq1, logic.getTerm_false());
    EXPECT_EQ(logic.getSymRef(eq1), logic.get_sym_Int_EQ());
}

TEST_F(LIALogicMkTermsTest, test_ReverseAuxRewrite) {

    static constexpr std::initializer_list<std::string_view> prefixes = {IteHandler::itePrefix, DivModConfig::divPrefix, DivModConfig::modPrefix};


    auto hasAuxSymbols = [this](PTRef tr) {
        class AuxSymbolMatcher {
            ArithLogic const & logic;

        public:
            AuxSymbolMatcher(ArithLogic const & logic) : logic(logic) {}
            bool operator()(PTRef tr) {
                std::string_view const name = logic.getSymName(tr);
                return std::any_of(prefixes.begin(), prefixes.end(), [&name](std::string_view const prefix) {
                    return name.compare(0, prefix.size(), prefix) == 0;
                });
            };
        };
        auto predicate = AuxSymbolMatcher(logic);
        auto config = TermCollectorConfig(predicate);
        TermVisitor(logic, config).visit(tr);
        return config.extractCollectedTerms().size() > 0;
    };

    PTRef a = logic.mkIntVar("a");
    PTRef c = logic.mkIntConst(5);
    PTRef modTerm = logic.mkMod(a, c);
    PTRef term = logic.mkEq(logic.getTerm_IntZero(), modTerm);

    PTRef res = logic.mkIntVar("res");
    PTRef cond = logic.mkBoolVar("cond");
    PTRef divTerm = logic.mkIntDiv(a, c);
    PTRef ite = logic.mkIte(cond, modTerm, divTerm);
    PTRef eq = logic.mkEq(res, ite);

    PTRef nested = logic.mkEq(logic.getTerm_IntZero(), logic.mkMod(ite, c));

    for (PTRef tr : {term, eq, nested}) {

        PTRef termWithAux = DivModRewriter(logic).rewrite(IteHandler(logic).rewrite(tr));
        ASSERT_TRUE(hasAuxSymbols(termWithAux));

        PTRef termWithoutAux = logic.removeAuxVars(termWithAux);
        std::cout << logic.pp(termWithoutAux) << std::endl;
        ASSERT_FALSE(hasAuxSymbols(termWithoutAux));
    }

}