//
// Created by Martin Blicha on 17.05.20.
//

#include <gtest/gtest.h>
#include <BoolRewriting.h>
#include <Logic.h>
#include <SMTConfig.h>


TEST(Rewriting_test, test_RewriteClassicConjunction)
{
    SMTConfig config;
    Logic logic{config};
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
    SMTConfig config;
    Logic logic{config};
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



