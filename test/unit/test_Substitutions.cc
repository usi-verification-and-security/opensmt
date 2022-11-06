/*
 *  Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include <gtest/gtest.h>
#include <Opensmt.h>

class LIASubstitutionsRegression: public ::testing::Test {
public:
    std::unique_ptr<Opensmt> getLIAOsmt() {
        return std::make_unique<Opensmt>(opensmt_logic::qf_lia, "test");
    }
};

class UFLRASubstitutionsRegression: public ::testing::Test {
protected:
    ArithLogic logic;
    SymRef f;
    PTRef a,b,c,x,y,z;
    PTRef fa,fb,fc,fx,fy,fz;
public:
    UFLRASubstitutionsRegression() : logic(opensmt::Logic_t::QF_UFLRA) {
        f = logic.declareFun("f", logic.getSort_real(), {logic.getSort_real()});
        x = logic.mkRealVar("x");
        y = logic.mkRealVar("y");
        z = logic.mkRealVar("z");
        a = logic.mkRealVar("a");
        b = logic.mkRealVar("b");
        c = logic.mkRealVar("c");
        fx = logic.mkUninterpFun(f,{x});
        fy = logic.mkUninterpFun(f,{y});
        fz = logic.mkUninterpFun(f,{z});
        fa = logic.mkUninterpFun(f,{a});
        fb = logic.mkUninterpFun(f,{b});
        fc = logic.mkUninterpFun(f,{c});
    }
};

TEST_F(LIASubstitutionsRegression, test_LIAsubstitution) {
    auto const osmt = getLIAOsmt();
    auto & mainSolver = osmt->getMainSolver();
    auto & lialogic = osmt->getLIALogic();
    PTRef x = lialogic.mkIntVar("x");
    PTRef y = lialogic.mkIntVar("y");
    PTRef two = lialogic.mkIntConst(2);
    PTRef eq = lialogic.mkEq(x, lialogic.mkTimes(two, y));
    PTRef a = lialogic.mkBoolVar("a");
    PTRef conj = lialogic.mkAnd(
            lialogic.mkImpl(a, lialogic.mkEq(x, lialogic.getTerm_IntOne())),
            lialogic.mkImpl(lialogic.mkNot(a), lialogic.mkEq(x, lialogic.getTerm_IntOne()))
            );
    PTRef fla = lialogic.mkAnd(conj, eq);
    // x = 2y  AND (a => x=1) AND (~a => x=1)
    char* msg;
    mainSolver.insertFormula(fla, &msg);
    auto res = mainSolver.check();
    ASSERT_EQ(res, s_False);
}

TEST_F(LIASubstitutionsRegression, test_InconsistentSubstitutions) {
    auto const osmt = getLIAOsmt();
    auto & lialogic = osmt->getLIALogic();
    PTRef x = lialogic.mkIntVar("x");
    PTRef y = lialogic.mkIntVar("y");
    PTRef one = lialogic.getTerm_IntOne();
    PTRef eq1 = lialogic.mkEq(x, y);
    PTRef eq2 = lialogic.mkEq(one, lialogic.mkMinus(x,y));
    Logic::SubstMap substMap;
    lialogic.arithmeticElimination({eq1,eq2}, substMap);
    ASSERT_TRUE(true);
}

TEST_F(LIASubstitutionsRegression, test_InconsistentSubstitutions_WithConstants) {
    auto const osmt = getLIAOsmt();
    auto & lialogic = osmt->getLIALogic();
    PTRef x = lialogic.mkIntVar("x");
    PTRef y = lialogic.mkIntVar("y");
    PTRef z = lialogic.mkIntVar("z");
    PTRef zero = lialogic.getTerm_IntZero();
    PTRef one = lialogic.getTerm_IntOne();
    PTRef eq1 = lialogic.mkEq(x, zero);
    PTRef eq2 = lialogic.mkEq(y, one);
    PTRef eq3 = lialogic.mkEq(z, one);
    PTRef eq4 = lialogic.mkEq(lialogic.mkPlus(vec<PTRef>{x,y,z}), one);
    Logic::SubstMap substMap;
    lialogic.arithmeticElimination({eq1,eq2,eq3,eq4}, substMap);
    ASSERT_TRUE(true);
}

TEST_F(LIASubstitutionsRegression, test_RedundantEquality) {
    auto const osmt = getLIAOsmt();
    auto & lialogic = osmt->getLIALogic();
    PTRef x = lialogic.mkIntVar("x");
    PTRef y = lialogic.mkIntVar("y");
    PTRef z = lialogic.mkIntVar("z");
    PTRef zero = lialogic.getTerm_IntZero();
    PTRef one = lialogic.getTerm_IntOne();
    PTRef eq1 = lialogic.mkEq(x, zero);
    PTRef eq2 = lialogic.mkEq(y, zero);
    PTRef eq3 = lialogic.mkEq(z, one);
    PTRef eq4 = lialogic.mkEq(lialogic.mkPlus(vec<PTRef>{x,y,z}), one);
    Logic::SubstMap substMap;
    lialogic.arithmeticElimination({eq1,eq2,eq3,eq4}, substMap);
    ASSERT_TRUE(true);
}

TEST_F(LIASubstitutionsRegression, test_TwoVarsEqual) {
    auto const osmt = getLIAOsmt();
    auto & lialogic = osmt->getLIALogic();
    PTRef x = lialogic.mkIntVar("x");
    PTRef y = lialogic.mkIntVar("y");
    PTRef eq1 = lialogic.mkEq(x, y);
    Logic::SubstMap substMap;
    lialogic.arithmeticElimination({eq1}, substMap);
    ASSERT_EQ(substMap.getSize(), 1);
    PTRef key = substMap.getKeys()[0];
    PTRef value = substMap[key];
    ASSERT_TRUE((key == x and value == y) or (key == y and value == x));
}

TEST_F(UFLRASubstitutionsRegression, test_NoProblematicSubstitutions) {
    vec<PTRef> equalities;
    equalities.push(logic.mkEq(x,fx));
    equalities.push(logic.mkEq(y,fy));
    equalities.push(logic.mkEq(z,fz));
    equalities.push(logic.mkEq(a,fa));
    equalities.push(logic.mkEq(b,fb));
    equalities.push(logic.mkEq(c,fc));
    Logic::SubstMap map;
    logic.arithmeticElimination(equalities, map);
    // Substitutions of the form 'var -> term' where term contains the variable are forbidden!
    EXPECT_FALSE(map.has(x));
    EXPECT_FALSE(map.has(y));
    EXPECT_FALSE(map.has(z));
    EXPECT_FALSE(map.has(a));
    EXPECT_FALSE(map.has(b));
    EXPECT_FALSE(map.has(c));
}
