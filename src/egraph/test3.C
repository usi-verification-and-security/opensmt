/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/


#include "Sort.h"
#include "SStore.h"
#include "SymStore.h"
#include "Symbol.h"
#include "PtStore.h"
#include "Pterm.h"
#include "Logic.h"
#include "Enode.h"
#include "EnodeStore.h"
#include "Egraph.h"
#include "TermMapper.h"

int main(int argc, char **argv) {
    SMTConfig cfg(argc, argv);
//    EnodeStore estore;
    SStore sort_store(cfg);
    SymStore sym_store;
    PtStore term_store(sym_store, sort_store);
    Logic logic(cfg, sort_store, sym_store, term_store);
    TermMapper tmap(logic);
    Egraph egraph(cfg, sort_store, sym_store, term_store, logic, tmap);

    assert(logic.setLogic("QF_UF"));

    Identifier i("TSort");
    Sort s(i);
    sort_store.insertStore(&s);
    logic.declare_sort_hook(&s);
    SRef sr = sort_store["TSort 0"];
    SRef bsr = sort_store["Bool 0"];
    // First arg is the return sort
    PTRef c_2_tr = logic.mkConst(sr, "c_2");
    PTRef c_3_tr = logic.mkConst(sr, "c_3");
    PTRef c16_tr = logic.mkConst(sr, "c16");

    // eq_1 : (= c_2 c16)
    vec<PTRef> eq_args;
    eq_args.push(c_2_tr);
    eq_args.push(c16_tr);

    PTRef eq_1 = logic.mkEq(eq_args);
    assert(logic.isEquality(eq_1));
    vec<PtPair> ites;
    vec<PTRef> nested_bools;

    egraph.declareTerm(PtChild(c_2_tr, eq_1, 0));
    egraph.declareTerm(PtChild(c16_tr, eq_1, 1));
    egraph.declareTerm(PtChild(eq_1, PTRef_Undef, -1));


    // eq_2 : (= c_3 c16)
    vec<PTRef> eq_args_2;
    eq_args_2.push(c_3_tr);
    eq_args_2.push(c16_tr);
    PTRef eq_2 = logic.mkEq(eq_args_2);

    egraph.declareTerm(PtChild(c_3_tr, eq_2, 0));
    egraph.declareTerm(PtChild(c16_tr, eq_2, 1));
    egraph.declareTerm(PtChild(eq_2, PTRef_Undef, -1));

    // eq_3 : (= c_2 c_3)
    vec<PTRef> eq_args_3;
    eq_args_3.push(c_2_tr);
    eq_args_3.push(c_3_tr);
    PTRef eq_3 = logic.mkEq(eq_args_3);

    egraph.declareTerm(PtChild(c_2_tr, eq_3, 0));
    egraph.declareTerm(PtChild(c_3_tr, eq_3, 1));
    egraph.declareTerm(PtChild(eq_3, PTRef_Undef, -1));


    // Assert the stuff

    lbool rval;
    rval = egraph.addDisequality(PtAsgn(eq_1, l_False));
    assert(rval == l_Undef);
//    rval = egraph.addFalse(eq_1);
//    assert(rval == l_Undef);

    rval = egraph.addEquality(PtAsgn(eq_2, l_True));
    assert(rval == l_Undef);
//    rval = egraph.addTrue(eq_2);
//    assert(rval == l_Undef);


    while (true) {
        PtAsgn_reason& r = egraph.getDeduction();

        if (r.tr == PTRef_Undef) { printf("No deductions\n"); break; }
        else 
            printf("Deduced term %s%s\n", r.sgn == l_True ? "" : "not ", logic.printTerm(r.tr));
    }

    printf("%s\n", egraph.printEqClass(logic.getTerm_true()));
    printf("%s\n", egraph.printEqClass(logic.getTerm_false()));


    return 0;
}
