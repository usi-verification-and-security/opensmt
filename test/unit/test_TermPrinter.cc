//
// Created by Antti on 18.02.22.
//

#include <gtest/gtest.h>
#include <Logic.h>
#include <TermPrinter.h>

class TermPrinterTest : public ::testing::Test {
public:
    Logic logic;
    TermPrinterTest() : logic{opensmt::Logic_t::QF_UF} {}

    PTRef buildExampleFormula1() {
        SRef sort = logic.declareUninterpretedSort("U");
        PTRef x = logic.mkVar(sort, "?20");
        PTRef y = logic.mkVar(sort, "????");
        SymRef g_s = logic.declareFun("g", sort, {sort, sort});
        SymRef h_s = logic.declareFun("h", sort, {sort});
        SymRef f_s = logic.declareFun("f", sort, {sort, sort, sort});
        PTRef g = logic.mkUninterpFun(g_s, {x, y});
        PTRef h = logic.mkUninterpFun(h_s, {y});
        PTRef f = logic.mkUninterpFun(f_s, {g, g, h});
        return logic.mkEq(f, h);
    }

    PTRef buildExampleFormula2() {
        vec<PTRef> shared;
        SRef sort = logic.declareUninterpretedSort("U");
        PTRef x = logic.mkVar(sort, "x");
        PTRef y = logic.mkVar(sort, "y");
        SymRef g_s = logic.declareFun("g", sort, {sort, sort});
        SymRef h_s = logic.declareFun("h", sort, {sort});
        SymRef f_s = logic.declareFun("f", sort, {sort, sort, sort});
        PTRef g = logic.mkUninterpFun(g_s, {x, y});
        PTRef h = logic.mkUninterpFun(h_s, {g});
        PTRef f = logic.mkUninterpFun(f_s, {g, g, h});
        return logic.mkEq(f, h);
    }

    PTRef buildExampleFormula3() {
        vec<PTRef> shared;
        SRef sort = logic.declareUninterpretedSort("U");
        PTRef x = logic.mkVar(sort, "x");
        PTRef y = logic.mkVar(sort, "y");
        SymRef g_s = logic.declareFun("g", sort, {sort, sort});
        SymRef h_s = logic.declareFun("h", sort, {sort, sort});
        SymRef f_s = logic.declareFun("f", sort, {sort, sort, sort});
        SymRef r_s = logic.declareFun("r", sort, {sort});
        PTRef g = logic.mkUninterpFun(g_s, {x, y});
        PTRef r = logic.mkUninterpFun(r_s, {y});
        PTRef h = logic.mkUninterpFun(h_s, {r, r});
        PTRef f = logic.mkUninterpFun(f_s, {g, g, h});
        return logic.mkEq(f, h);
    }
};

TEST_F(TermPrinterTest, test_TermPrinting) {
    PTRef ex1 = buildExampleFormula1();
    PTRef ex2 = buildExampleFormula2();
    PTRef ex3 = buildExampleFormula3();
    for (PTRef ex : {ex1, ex2, ex3}) {
        ReferenceCounterConfig refCounter(logic);
        TermVisitor(logic, refCounter).visit(ex);
        std::cout << TermPrinter(logic).print(ex) << std::endl;
        ASSERT_EQ (TermPrinter(logic).print(ex), logic.pp(ex));
    }

    for (PTRef ex : {ex1, ex2, ex3}) {
        DagPrinter printer(logic);
        std::cout << "===================================" << std::endl;
        std::cout << logic.pp(ex) << std::endl;
        std::cout << " -> " << std::endl;
        std::cout << printer.print(ex) << std::endl;
    }
}
