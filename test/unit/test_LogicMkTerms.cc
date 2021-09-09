//
// Created by Antti on 31.03.20.
//
#include <gtest/gtest.h>
#include <Logic.h>

#include <TreeOps.h>


class LogicMkTermsTest: public ::testing::Test {
public:
    Logic logic;
    LogicMkTermsTest(): logic{} {}
};

TEST_F(LogicMkTermsTest, test_Distinct){
    SRef ufsort = logic.declareSort("U", nullptr);
    PTRef x = logic.mkVar(ufsort, "x");
    PTRef y = logic.mkVar(ufsort, "y");
    PTRef distinct = logic.mkDistinct({x,y});
    ASSERT_NE(distinct, logic.getTerm_false());
    ASSERT_NE(distinct, logic.getTerm_true());

    distinct = logic.mkDistinct({x});
    ASSERT_EQ(distinct, logic.getTerm_true());

    distinct = logic.mkDistinct({});
    ASSERT_EQ(distinct, logic.getTerm_true());

    distinct = logic.mkDistinct({x,x});
    ASSERT_EQ(distinct, logic.getTerm_false());

    distinct = logic.mkDistinct({x,y,x});
    ASSERT_EQ(distinct, logic.getTerm_false());

    distinct = logic.mkDistinct({x,y});
    // MB: dinstinct(x,y) is equivalent to not equal(x,y) and the second version is preferred
    ASSERT_TRUE(logic.isNot(distinct) && logic.isEquality(logic.getPterm(distinct)[0]));

    PTRef b1 = logic.mkBoolVar("b1");
    PTRef b2 = logic.mkBoolVar("b2");
    PTRef b3 = logic.mkBoolVar("b3");

    distinct = logic.mkDistinct({b1,b2,b3});
    ASSERT_EQ(distinct, logic.getTerm_false());

    PTRef z = logic.mkVar(ufsort, "z");
    distinct = logic.mkDistinct({x, y, z});
    ASSERT_TRUE(logic.isDisequality(distinct));
}

TEST_F(LogicMkTermsTest, test_ManyDistinct) {
    SRef ufsort = logic.declareSort("U", nullptr);
    vec<PTRef> names;
    for (int i = 0; i < 9; i++) {
        std::string name = "x" + std::to_string(i);
        names.push(logic.mkVar(ufsort, name.c_str()));
    }
    vec<PTRef> distincts1;
    for (int i = 0; i < 9; i++) {
        for (int j = i+1; j < 9; j++) {
            for (int k = j+1; k < 9; k++) {
                distincts1.push(logic.mkDistinct({names[i], names[j], names[k]}));
            }
        }
    }
    vec<PTRef> distincts2;
    for (int i = 0; i < 9; i++) {
        for (int j = i+1; j < 9; j++) {
            for (int k = j+1; k < 9; k++) {
                distincts2.push(logic.mkDistinct({names[j], names[i], names[k]}));
            }
        }
    }
    vec<PTRef> distincts3;
    for (int i = 0; i < 9; i++) {
        for (int j = i+1; j < 9; j++) {
            for (int k = j+1; k < 9; k++) {
                distincts3.push(logic.mkDistinct({names[k], names[i], names[j]}));
            }
        }
    }
    for (int i = 0; i < distincts1.size(); i++) {
        ASSERT_EQ(distincts1[i].x, distincts2[i].x);
        ASSERT_EQ(distincts1[i].x, distincts3[i].x);
    }
}

TEST_F(LogicMkTermsTest, testMkOrTautology) {
    PTRef a = logic.mkBoolVar("a");
    PTRef nota = logic.mkNot(a);
    ASSERT_EQ(logic.mkOr(a, nota), logic.getTerm_true());
}

TEST_F(LogicMkTermsTest, testMkAndContradiction) {
    PTRef a = logic.mkBoolVar("a");
    PTRef nota = logic.mkNot(a);
    ASSERT_EQ(logic.mkAnd(a, nota), logic.getTerm_false());
}

TEST_F(LogicMkTermsTest, testIteration) {
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef conj = logic.mkAnd({a, b});
    PTRef c = logic.mkBoolVar("c");
    PTRef disj = logic.mkOr({a, b, c});

    for (auto tr : {a, b, c}) {
        int count = 0;
        for (auto ch : logic.getPterm(tr)) {
            (void)ch;
            count++;
        }
        ASSERT_EQ(count, 0);
    }

    for (auto tr : {conj, disj}) {
        Pterm const &t = logic.getPterm(tr);
        for (auto ch : t) {
            bool found = false;
            for (int i = 0; i < t.size(); i++) {
                found |= ch == t[i];
            }
            ASSERT_TRUE(found);
        }
    }
}

TEST_F(LogicMkTermsTest, testUniqueAbstractValue) {
    PTRef uniq1 = logic.mkUniqueAbstractValue(logic.getSort_bool());
    PTRef uniq2 = logic.mkUniqueAbstractValue(logic.getSort_bool());
    ASSERT_NE(uniq1, uniq2);
}

TEST_F(LogicMkTermsTest, testAtom_Bool) {
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    EXPECT_TRUE(logic.isAtom(a));
    EXPECT_FALSE(logic.isAtom(logic.mkNot(a)));

    EXPECT_FALSE(logic.isAtom(logic.mkAnd(a,b)));
    EXPECT_FALSE(logic.isAtom(logic.mkOr(a,b)));
    EXPECT_FALSE(logic.isAtom(logic.mkXor(a,b)));
    EXPECT_FALSE(logic.isAtom(logic.mkImpl(a,b)));
    // Boolean equivalence is not considered an atom!
    EXPECT_FALSE(logic.isAtom(logic.mkEq(a,b)));
    // Boolean ITE is not considered an atom!
    EXPECT_FALSE(logic.isAtom(logic.mkIte(c,a,b)));

    EXPECT_TRUE(logic.isAtom(logic.getTerm_true()));
    EXPECT_TRUE(logic.isAtom(logic.getTerm_false()));
}


TEST_F(LogicMkTermsTest, testAtom_UF) {
    SRef sref = logic.declareSort("U", nullptr);
    PTRef a = logic.mkVar(sref, "a");
    PTRef b = logic.mkVar(sref, "b");
    PTRef c = logic.mkVar(sref, "c");
    PTRef eq = logic.mkEq(a,b);
    PTRef dist = logic.mkDistinct({a,b,c});
    EXPECT_TRUE(logic.isAtom(eq));
    EXPECT_FALSE(logic.isAtom(logic.mkNot(eq)));

    EXPECT_TRUE(logic.isAtom(dist));
    EXPECT_FALSE(logic.isAtom(logic.mkNot(dist)));

    SymRef predicate = logic.declareFun("p", logic.getSort_bool(), {sref}, nullptr);
    PTRef pa = logic.mkUninterpFun(predicate, {a});
    EXPECT_TRUE(logic.isAtom(pa));
    EXPECT_FALSE(logic.isAtom(logic.mkNot(pa)));
}

bool contains(vec<PTRef> const& v, PTRef t) {
    for (PTRef e : v) {
        if (t == e) {
            return true;
        }
    }
    return false;
}

TEST_F(LogicMkTermsTest, testTopLevelConjuncts_flat) {
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef fla = logic.mkAnd({a,b,c});
    auto conjuncts = topLevelConjuncts(logic, fla);
    ASSERT_EQ(conjuncts.size(), 3);
    for (PTRef p : {a,b,c}) {
        EXPECT_TRUE(contains(conjuncts, p));
    }
}

TEST_F(LogicMkTermsTest, testTopLevelConjuncts_nested) {
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef d = logic.mkBoolVar("d");
    PTRef fla = logic.mkAnd(logic.mkAnd(a,b), logic.mkAnd(c,d));
    auto conjuncts = topLevelConjuncts(logic, fla);
    ASSERT_EQ(conjuncts.size(), 4);
    for (PTRef p : {a,b,c,d}) {
        EXPECT_TRUE(contains(conjuncts, p));
    }
}

TEST_F(LogicMkTermsTest, testTopLevelConjuncts_noDuplicates) {
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef c = logic.mkBoolVar("c");
    PTRef fla = logic.mkAnd(logic.mkAnd(a,b), logic.mkAnd(c,a));
    auto conjuncts = topLevelConjuncts(logic, fla);
    ASSERT_EQ(conjuncts.size(), 3);
    for (PTRef p : {a,b,c}) {
        EXPECT_TRUE(contains(conjuncts, p));
    }
}

TEST_F(LogicMkTermsTest, testTopLevelConjuncts_notConjunction) {
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    auto conjuncts1 = topLevelConjuncts(logic, a);
    ASSERT_EQ(conjuncts1.size(), 1);
    EXPECT_EQ(conjuncts1[0], a);
    PTRef fla = logic.mkOr(a,b);
    auto conjuncts2 = topLevelConjuncts(logic, fla);
    ASSERT_EQ(conjuncts2.size(), 1);
    EXPECT_EQ(conjuncts2[0], fla);
}
