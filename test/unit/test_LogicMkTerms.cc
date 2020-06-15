//
// Created by Antti on 31.03.20.
//
#include <gtest/gtest.h>
#include <Logic.h>
#include <SMTConfig.h>

class LogicMkTermsTest: public ::testing::Test {
public:
    SMTConfig config;
    Logic logic;
    LogicMkTermsTest(): logic{config} {}
};

TEST_F(LogicMkTermsTest, test_Distinct){
    SMTConfig config;
    Logic logic{config};

    SRef ufsort = logic.declareSort("U", nullptr);
    PTRef x = logic.mkVar(ufsort, "x");
    PTRef y = logic.mkVar(ufsort, "y");
    vec<PTRef> args;
    args.push(x);
    args.push(y);
    PTRef distinct = logic.mkDistinct(args);
    ASSERT_NE(distinct, logic.getTerm_false());
    ASSERT_NE(distinct, logic.getTerm_true());

    args.clear();
    args.push(x);
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_true());

    args.clear();
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_true());

    args.push(x);
    args.push(x);
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_false());

    args.clear();
    args.push(x);
    args.push(y);
    args.push(x);
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_false());



    args.clear();
    args.push(x);
    args.push(y);
    distinct = logic.mkDistinct(args);
    // MB: dinstinct(x,y) is equivalent to not equal(x,y) and the second version is preferred
    ASSERT_TRUE(logic.isNot(distinct) && logic.isEquality(logic.getPterm(distinct)[0]));

    PTRef b1 = logic.mkBoolVar("b1");
    PTRef b2 = logic.mkBoolVar("b2");
    PTRef b3 = logic.mkBoolVar("b3");

    args.clear();
    args.push(b1);
    args.push(b2);
    args.push(b3);
    distinct = logic.mkDistinct(args);
    ASSERT_EQ(distinct, logic.getTerm_false());
}

TEST_F(LogicMkTermsTest, test_ManyDistinct) {
    SMTConfig config;
    Logic logic{config};

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
                vec<PTRef> triple{names[i], names[j], names[k]};
                distincts1.push(logic.mkDistinct(triple));
            }
        }
    }
    vec<PTRef> distincts2;
    for (int i = 0; i < 9; i++) {
        for (int j = i+1; j < 9; j++) {
            for (int k = j+1; k < 9; k++) {
                vec<PTRef> triple{names[j], names[i], names[k]};
                distincts2.push(logic.mkDistinct(triple));
            }
        }
    }
    vec<PTRef> distincts3;
    for (int i = 0; i < 9; i++) {
        for (int j = i+1; j < 9; j++) {
            for (int k = j+1; k < 9; k++) {
                vec<PTRef> triple{names[k], names[i], names[j]};
                distincts3.push(logic.mkDistinct(triple));
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
