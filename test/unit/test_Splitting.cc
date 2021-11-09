//
// Created by Antti on 30.09.21.
//

#include <gtest/gtest.h>
#include <Logic.h>

class SplitTest : public ::testing::Test {
protected:
    SplitTest() : logic{} {}
    Logic logic;
};

TEST_F(SplitTest, test_TermPrinting) {
    char * msg;
    SRef U = logic.declareSort("U");
    SymRef sr = logic.declareFun("f", U, {U, U}, &msg, false);
    PTRef a = logic.mkVar(U, "a");
    PTRef f_a = logic.mkUninterpFun(sr, {a, a});
    char * str_p = logic.printTerm(f_a);
    std::string str(str_p);
    std::string reference = "(f a a)";
    free(str_p);
    std::cout << str << std::endl;
    ASSERT_EQ(str.compare(reference), 0);
}