//
// Created by Martin Blicha on 2018-12-20.
//

#include <gtest/gtest.h>
#include <Logic.h>
#include <Substitutor.h>

class GetFactsTest : public ::testing::Test {
protected:
    GetFactsTest(): logic{} {}
    virtual void SetUp() {
        ufsort = logic.declareSort("U");
        x = logic.mkVar(ufsort, "x");
        y = logic.mkVar(ufsort, "y");
    }
    Logic logic;
    SRef ufsort;
    PTRef x;
    PTRef y;
    PTRef z;
};


TEST_F(GetFactsTest, test_UnitFact){
    PTRef eq = logic.mkEq(x,y);
    MapWithKeys<PTRef,lbool,PTRefHash> newFacts;
    logic.getNewFacts(eq, newFacts);
    ASSERT_TRUE(newFacts.has(eq));
    EXPECT_EQ(newFacts[eq], l_True);
}

TEST_F(GetFactsTest, test_NegatedUnitFact){
    PTRef eq = logic.mkEq(x,y);
    PTRef neq = logic.mkNot(eq);
    MapWithKeys<PTRef,lbool,PTRefHash> newFacts;
    // MB: Currently it does not learn inequalities. Should it?
    logic.getNewFacts(neq, newFacts);
//    ASSERT_TRUE(newFacts.has(neq));
//    EXPECT_EQ(newFacts[eq], l_True);
}

TEST_F(GetFactsTest, test_NegatedBoolLiteral){
    PTRef var = logic.mkBoolVar("a");
    PTRef neq = logic.mkNot(var);
    MapWithKeys<PTRef,lbool,PTRefHash> newFacts;
    logic.getNewFacts(neq, newFacts);
    ASSERT_TRUE(newFacts.has(var));
    EXPECT_EQ(newFacts[var], l_False);
}

TEST_F(GetFactsTest, test_MultipleFacts){
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef eq = logic.mkEq(x,y);
    PTRef neq = logic.mkNot(eq);
    PTRef conj = logic.mkAnd(a, logic.mkNot(logic.mkOr(b, neq)));
    MapWithKeys<PTRef,lbool,PTRefHash> newFacts;
    logic.getNewFacts(conj, newFacts);
    ASSERT_TRUE(newFacts.has(a));
    ASSERT_TRUE(newFacts.has(b));
    ASSERT_TRUE(newFacts.has(eq));
    EXPECT_EQ(newFacts[a], l_True);
    EXPECT_EQ(newFacts[b], l_False);
    EXPECT_EQ(newFacts[eq], l_True);
}

//========================== TEST for retrieving sustituitions =========================================================


class RetrieveSubstitutionTest : public ::testing::Test {
protected:
    RetrieveSubstitutionTest(): logic{} {}
    virtual void SetUp() {
        ufsort = logic.declareSort("U");
        x = logic.mkVar(ufsort, "x");
        y = logic.mkVar(ufsort, "y");
        z = logic.mkVar(ufsort, "z");
        c = logic.mkConst(ufsort, "c");
        char* msg;
        f = logic.declareFun("f", ufsort, {ufsort}, &msg, false);
    }
    Logic logic;
    SRef ufsort;
    PTRef x;
    PTRef y;
    PTRef z;
    PTRef c;
    SymRef f;
};

TEST_F(RetrieveSubstitutionTest, test_VarVarSubstituition) {
    PTRef eq = logic.mkEq(x,y);
    vec<PtAsgn> facts;
    facts.push(PtAsgn{eq, l_True});
    auto subst = logic.retrieveSubstitutions(facts);
    ASSERT_TRUE(subst.second.has(x));
    EXPECT_EQ(subst.second[x], y);
}

TEST_F(RetrieveSubstitutionTest, test_AtomSubstituition) {
    PTRef a = logic.mkBoolVar("a");
    vec<PtAsgn> facts;
    facts.push(PtAsgn{a, l_True});
    auto subst = logic.retrieveSubstitutions(facts);
    ASSERT_TRUE(subst.second.has(a));
    EXPECT_EQ(subst.second[a], logic.getTerm_true());
}

TEST_F(RetrieveSubstitutionTest, test_ConstantSubstituition) {
    PTRef fx = logic.mkUninterpFun(f, {x});
    PTRef eq = logic.mkEq(fx, c);
    vec<PtAsgn> facts;
    facts.push(PtAsgn{eq, l_True});
    auto subst = logic.retrieveSubstitutions(facts);
    ASSERT_TRUE(subst.second.has(fx));
    EXPECT_EQ(subst.second[fx], c);
}

TEST_F(RetrieveSubstitutionTest, test_NestedSubstitution) {
    PTRef fx = logic.mkUninterpFun(f, {x});
    PTRef fy = logic.mkUninterpFun(f, {y});
    PTRef eq = logic.mkEq(fx, y);
    PTRef eq2 = logic.mkEq(fy, z);
    vec<PtAsgn> facts;
    facts.push(PtAsgn{eq, l_True});
    facts.push(PtAsgn{eq2, l_True});
    auto subst = logic.retrieveSubstitutions(facts);
    ASSERT_TRUE(subst.second.has(z));
    ASSERT_TRUE(subst.second.has(y));
    EXPECT_EQ(subst.second[z], fy);
    EXPECT_EQ(subst.second[y], fx);
}

//========================== TEST for applying sustituitions ===========================================================
class ApplySubstitutionTest : public ::testing::Test {
protected:
    ApplySubstitutionTest(): logic{} {}
    virtual void SetUp() {
        ufsort = logic.declareSort("U");
        x = logic.mkVar(ufsort, "x");
        y = logic.mkVar(ufsort, "y");
        z = logic.mkVar(ufsort, "z");
        c = logic.mkConst(ufsort, "c");
        char* msg;
        f = logic.declareFun("f", ufsort, {ufsort}, &msg, false);
    }
    Logic logic;
    SRef ufsort;
    PTRef x;
    PTRef y;
    PTRef z;
    PTRef c;
    SymRef f;
};

// MB: Logic::varsubstitute does only one-sweep substitution, it does not check the new terms for new possibilities

TEST_F(ApplySubstitutionTest, test_BoolAtomSub) {
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef fla = logic.mkAnd(a, logic.mkNot(b));
    Logic::SubstMap subst;
    subst.insert(b, logic.getTerm_true());
    PTRef res = Substitutor(logic, subst).rewrite(fla);
    EXPECT_EQ(res, logic.getTerm_false());
}

TEST_F(ApplySubstitutionTest, test_VarVarSub) {
    PTRef fla = logic.mkEq(x, z);
    Logic::SubstMap subst;
    subst.insert(x, y);
    PTRef res = Substitutor(logic, subst).rewrite(fla);
    EXPECT_EQ(res, logic.mkEq(y,z));
}

TEST_F(ApplySubstitutionTest, test_NestedSub) {
    PTRef fy = logic.mkUninterpFun(f, {y});
    PTRef fz = logic.mkUninterpFun(f, {z});
    PTRef fla = logic.mkEq(x, logic.mkUninterpFun(f, {fz}));
    Logic::SubstMap subst;
    subst.insert(x, fy);
    subst.insert(y, fz);
    PTRef res = Substitutor(logic, subst).rewrite(fla);
//    EXPECT_EQ(res, logic.getTerm_true()); // MB: This requires something like fixed-point substitution
    EXPECT_EQ(res, logic.mkEq(fy, logic.mkUninterpFun(f, {fz})));
}

//========================== TEST for transitive closure of substitutions ===========================================================
TEST(SubstitutionTransitiveClosure, test_twoStepSubstitution) {
    Logic logic;
    Logic::SubstMap substitutions;
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef d = logic.mkBoolVar("d");
    substitutions.insert(a, logic.mkAnd(b,c));
    substitutions.insert(b, c);
    substitutions.insert(c, d);
    logic.substitutionsTransitiveClosure(substitutions);
    ASSERT_EQ(substitutions.getSize(), 3);
    ASSERT_EQ(substitutions[a], d);
}

