//
// Created by Martin Blicha on 31.10.18.
//

#include <gtest/gtest.h>
#include <BoolRewriting.h>
#include <Logic.h>
#include <SMTConfig.h>

TEST(SimplifyUnderAssignment_test, test_Simple_Conjunction)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef conj = logic.mkAnd(a, logic.mkOr(
            logic.mkNot(a),
            b
            ));
    PTRef res = simplifyUnderAssignment(logic, conj);
    ASSERT_EQ(res, logic.mkAnd(a,b));
}

TEST(SimplifyUnderAssignment_test, test_ConjunctionToConstant)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef conj = logic.mkAnd(a, logic.mkAnd(logic.mkNot(a), b));
    PTRef res = simplifyUnderAssignment(logic, conj);
    ASSERT_EQ(res, logic.getTerm_false());
}

TEST(SimplifyUnderAssignment_test, test_DisjunctionToConstant)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef disj = logic.mkOr(a, logic.mkOr(logic.mkNot(a), b));
    PTRef res = simplifyUnderAssignment(logic, disj);
    ASSERT_EQ(res, logic.getTerm_true());
}

TEST(SimplifyUnderAssignment_test, test_Simple_Disjunction)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef disj = logic.mkOr(a, logic.mkAnd(
            logic.mkNot(a),
            b
    ));
    PTRef res = simplifyUnderAssignment(logic, disj);
    ASSERT_EQ(res, logic.mkOr(a,b));
}

TEST(SimplifyUnderAssignment_test, test_Do_Not_Simplify_Shared)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef conj = logic.mkAnd(a,b);
    PTRef cdisj = logic.mkOr(c, conj);
    PTRef top = logic.mkAnd(
            cdisj,
            logic.mkOr(logic.mkNot(a), conj)
            );
    PTRef res = simplifyUnderAssignment(logic, top);
    ASSERT_EQ(res, top);
}

TEST(SimplifyUnderAssignment_test, test_NestedStructure)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef nota = logic.mkNot(a);
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef top = logic.mkAnd(
            logic.mkOr(nota, logic.mkAnd(b, nota)),
            c
    );
    PTRef res = simplifyUnderAssignment(logic, top);
    ASSERT_EQ(res, logic.mkAnd(nota, c));
}

TEST(SimplifyUnderAssignemnt_test, test_BooleanEquality)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef nota = logic.mkNot(a);
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef eq = logic.mkEq(a,b);
    vec<PTRef> args;
    args.push(eq);
    args.push(nota);
    args.push(logic.mkOr(a, logic.mkNot(eq)));
    PTRef top = logic.mkAnd(args);
    PTRef res = simplifyUnderAssignment(logic, top);
    ASSERT_TRUE(res == logic.getTerm_false());
}

// ===================== Tests of agressive simplification based on dominators ========================================
TEST(SimplifyUnderAssignmentAggressive_test, test_Simple_Conjunction)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef conj = logic.mkAnd(a, logic.mkOr(
            logic.mkNot(a),
            b
    ));
    PTRef res = simplifyUnderAssignment_Aggressive(conj, logic);
    ASSERT_EQ(res, logic.mkAnd(a,b));
}

TEST(SimplifyUnderAssignmentAggressive_test, test_ConjunctionToConstant)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef conj = logic.mkAnd(a, logic.mkAnd(logic.mkNot(a), b));
    PTRef res = simplifyUnderAssignment_Aggressive(conj, logic);
    ASSERT_EQ(res, logic.getTerm_false());
}

TEST(SimplifyUnderAssignmentAggressive_test, test_DisjunctionToConstant)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef disj = logic.mkOr(a, logic.mkOr(logic.mkNot(a), b));
    PTRef res = simplifyUnderAssignment_Aggressive(disj, logic);
    ASSERT_EQ(res, logic.getTerm_true());
}

TEST(SimplifyUnderAssignmentAggressive_test, test_Simple_Disjunction)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef disj = logic.mkOr(a, logic.mkAnd(
            logic.mkNot(a),
            b
    ));
    PTRef res = simplifyUnderAssignment_Aggressive(disj, logic);
    ASSERT_EQ(res, logic.mkOr(a,b));
}

TEST(SimplifyUnderAssignmentAggressive_test, test_Do_Not_Simplify)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef conj = logic.mkAnd(a,b);
    PTRef cdisj = logic.mkOr(c, conj);
    PTRef top = logic.mkAnd(
            cdisj,
            logic.mkOr(logic.mkNot(a), conj)
    );
    PTRef res = simplifyUnderAssignment(logic, top);
    ASSERT_EQ(res, top);
}

TEST(SimplifyUnderAssignmentAggressive_test, test_NestedStructure)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef nota = logic.mkNot(a);
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef top = logic.mkAnd(
            logic.mkOr(nota, logic.mkAnd(b, nota)),
            c
    );
    PTRef res = simplifyUnderAssignment_Aggressive(top, logic);
    ASSERT_EQ(res, logic.mkAnd(nota, c));
}

TEST(SimplifyUnderAssignmentAggressive_test, test_BooleanEquality)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef nota = logic.mkNot(a);
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef eq = logic.mkEq(a,b);
    vec<PTRef> args;
    args.push(eq);
    args.push(nota);
    args.push(logic.mkOr(a, logic.mkNot(eq)));
    PTRef top = logic.mkAnd(args);
    PTRef res = simplifyUnderAssignment_Aggressive(top, logic);
    ASSERT_TRUE(res == logic.getTerm_false());
}

TEST(SimplifyUnderAssignmentAggressive_test, test_SimplifyByDominator)
{
    SMTConfig config;
    Logic logic{config};
    PTRef a = logic.mkBoolVar("a");
    PTRef nota = logic.mkNot(a);
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef notb = logic.mkNot(b);
    PTRef conj = logic.mkAnd(nota, b);
    vec<PTRef> args;
    args.push(a);
    args.push(logic.mkOr(notb, conj));
    args.push(logic.mkOr(c, conj));
    PTRef top = logic.mkAnd(args);
    PTRef res = simplifyUnderAssignment_Aggressive(top, logic);
    args.clear();
    args.push(a);
    args.push(notb);
    args.push(c);
    ASSERT_TRUE(res == logic.mkAnd(args));
}




