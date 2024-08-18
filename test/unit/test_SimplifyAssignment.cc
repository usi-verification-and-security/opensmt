//
// Created by Martin Blicha on 31.10.18.
//

#include <gtest/gtest.h>
#include <simplifiers/BoolRewriting.h>
#include <logics/Logic.h>

namespace opensmt {

class SimplifyUnderAssignment_test : public ::testing::Test {
public:
    Logic logic;
    PTRef a;
    PTRef b;
    PTRef c;
    SimplifyUnderAssignment_test() : logic{Logic_t::QF_BOOL}, a(logic.mkBoolVar("a")), b(logic.mkBoolVar("b")), c(logic.mkBoolVar("c")) {}
};

TEST_F(SimplifyUnderAssignment_test, test_Simple_Conjunction)
{
    PTRef conj = logic.mkAnd(a, logic.mkOr(
            logic.mkNot(a),
            b
            ));
    PTRef res = simplifyUnderAssignment(logic, conj);
    ASSERT_EQ(res, logic.mkAnd(a,b));
}

TEST_F(SimplifyUnderAssignment_test, test_ConjunctionToConstant)
{
    PTRef conj = logic.mkAnd(a, logic.mkAnd(logic.mkNot(a), b));
    PTRef res = simplifyUnderAssignment(logic, conj);
    ASSERT_EQ(res, logic.getTerm_false());
}

TEST_F(SimplifyUnderAssignment_test, test_DisjunctionToConstant)
{
    PTRef disj = logic.mkOr(a, logic.mkOr(logic.mkNot(a), b));
    PTRef res = simplifyUnderAssignment(logic, disj);
    ASSERT_EQ(res, logic.getTerm_true());
}

TEST_F(SimplifyUnderAssignment_test, test_Simple_Disjunction)
{
    PTRef disj = logic.mkOr(a, logic.mkAnd(
            logic.mkNot(a),
            b
    ));
    PTRef res = simplifyUnderAssignment(logic, disj);
    ASSERT_EQ(res, logic.mkOr(a,b));
}

TEST_F(SimplifyUnderAssignment_test, test_Do_Not_Simplify_Shared)
{
    PTRef conj = logic.mkAnd(a,b);
    PTRef cdisj = logic.mkOr(c, conj);
    PTRef top = logic.mkAnd(
            cdisj,
            logic.mkOr(logic.mkNot(a), conj)
            );
    PTRef res = simplifyUnderAssignment(logic, top);
    ASSERT_EQ(res, top);
}

TEST_F(SimplifyUnderAssignment_test, test_NestedStructure)
{
    PTRef nota = logic.mkNot(a);
    PTRef top = logic.mkAnd(
            logic.mkOr(nota, logic.mkAnd(b, nota)),
            c
    );
    PTRef res = simplifyUnderAssignment(logic, top);
    ASSERT_EQ(res, logic.mkAnd(nota, c));
}

TEST_F(SimplifyUnderAssignment_test, test_BooleanEquality)
{
    PTRef nota = logic.mkNot(a);
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
TEST_F(SimplifyUnderAssignment_test, test_Simple_Conjunction_Aggressive)
{
    PTRef conj = logic.mkAnd(a, logic.mkOr(
            logic.mkNot(a),
            b
    ));
    PTRef res = simplifyUnderAssignment_Aggressive(conj, logic);
    ASSERT_EQ(res, logic.mkAnd(a,b));
}

TEST_F(SimplifyUnderAssignment_test, test_ConjunctionToConstant_Aggressive)
{
    PTRef conj = logic.mkAnd(a, logic.mkAnd(logic.mkNot(a), b));
    PTRef res = simplifyUnderAssignment_Aggressive(conj, logic);
    ASSERT_EQ(res, logic.getTerm_false());
}

TEST_F(SimplifyUnderAssignment_test, test_DisjunctionToConstant_Aggressive)
{
    PTRef disj = logic.mkOr(a, logic.mkOr(logic.mkNot(a), b));
    PTRef res = simplifyUnderAssignment_Aggressive(disj, logic);
    ASSERT_EQ(res, logic.getTerm_true());
}

TEST_F(SimplifyUnderAssignment_test, test_Simple_Disjunction_Aggressive)
{
    PTRef disj = logic.mkOr(a, logic.mkAnd(
            logic.mkNot(a),
            b
    ));
    PTRef res = simplifyUnderAssignment_Aggressive(disj, logic);
    ASSERT_EQ(res, logic.mkOr(a,b));
}

TEST_F(SimplifyUnderAssignment_test, test_Do_Not_Simplify_Aggressive)
{
    PTRef conj = logic.mkAnd(a,b);
    PTRef cdisj = logic.mkOr(c, conj);
    PTRef top = logic.mkAnd(
            cdisj,
            logic.mkOr(logic.mkNot(a), conj)
    );
    PTRef res = simplifyUnderAssignment(logic, top);
    ASSERT_EQ(res, top);
}

TEST_F(SimplifyUnderAssignment_test, test_NestedStructure_Aggressive)
{
    PTRef nota = logic.mkNot(a);
    PTRef top = logic.mkAnd(
            logic.mkOr(nota, logic.mkAnd(b, nota)),
            c
    );
    PTRef res = simplifyUnderAssignment_Aggressive(top, logic);
    ASSERT_EQ(res, logic.mkAnd(nota, c));
}

TEST_F(SimplifyUnderAssignment_test, test_BooleanEquality_Aggressive)
{
    PTRef nota = logic.mkNot(a);
    PTRef eq = logic.mkEq(a,b);
    vec<PTRef> args;
    args.push(eq);
    args.push(nota);
    args.push(logic.mkOr(a, logic.mkNot(eq)));
    PTRef top = logic.mkAnd(args);
    PTRef res = simplifyUnderAssignment_Aggressive(top, logic);
    ASSERT_TRUE(res == logic.getTerm_false());
}

TEST_F(SimplifyUnderAssignment_test, test_SimplifyByDominator_Aggressive)
{
    PTRef nota = logic.mkNot(a);
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

}
