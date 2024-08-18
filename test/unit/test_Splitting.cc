//
// Created by Antti on 30.09.21.
//

#include <gtest/gtest.h>
#include <logics/Logic.h>

namespace opensmt {

class SplitTest : public ::testing::Test {
protected:
    SplitTest() : logic{Logic_t::QF_UF} {}
    Logic logic;
};

TEST_F(SplitTest, test_TermPrinting) {
    SRef U = logic.declareUninterpretedSort("U");
    SymRef sr = logic.declareFun("f", U, {U, U});
    PTRef a = logic.mkVar(U, "a");
    PTRef f_a = logic.mkUninterpFun(sr, {a, a});
    std::string str = logic.printTerm(f_a);
    std::string reference = "(f a a)";
    std::cout << str << std::endl;
    ASSERT_EQ(str.compare(reference), 0);
}

}
