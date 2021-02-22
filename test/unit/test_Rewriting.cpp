//
// Created by Martin Blicha on 17.05.20.
//

#include <gtest/gtest.h>
#include <BoolRewriting.h>
#include <Logic.h>
#include <LRALogic.h>
#include <ArithmeticEqualityRewriter.h>


TEST(Rewriting_test, test_RewriteClassicConjunction)
{
    Logic logic;
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef d = logic.mkBoolVar("d");
    PTRef conj = logic.mkAnd(logic.mkAnd(a,b), logic.mkAnd(c,d));
    PTRef res = ::rewriteMaxArityClassic(logic, conj);
    vec<PTRef> args {a,b,c,d};
    ASSERT_EQ(res, logic.mkAnd(args));
}

TEST(Rewriting_test, test_RewriteClassicWithSimplification)
{
    Logic logic;
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef d = logic.mkBoolVar("d");
    PTRef l3 = logic.mkAnd(a, logic.mkAnd(b, logic.mkNot(a)));
    PTRef l2 = logic.mkOr(l3, logic.mkAnd(c,d));
    PTRef l1 = logic.mkAnd(b, l2);
    // l1 is (and b (or (and c d) (and a (and b (not a)))))
    // which is equivalent to (and b c d)
    PTRef res = ::rewriteMaxArityClassic(logic, l1);
//    std::cout << logic.printTerm(res) << std::endl;
    vec<PTRef> args {b,c,d};
    ASSERT_EQ(res, logic.mkAnd(args));
}

TEST(Rewriting_test, test_RewriteEquality)
{
    LRALogic logic;
    PTRef x = logic.mkNumVar("x");
    PTRef y = logic.mkNumVar("y");
    PTRef eq = logic.mkEq(x,y);
    ArithmeticEqualityRewriter rewriter(logic);
    PTRef res = rewriter.rewrite(eq);
    ASSERT_EQ(res, logic.mkAnd(logic.mkNumGeq(x,y), logic.mkNumLeq(x,y)));
    ASSERT_EQ(res, rewriter.rewrite(res));
}



