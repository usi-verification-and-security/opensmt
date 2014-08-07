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

    const char* msg;
    SRef sr = logic.declareSort("U", &msg);
    if (sr == SRef_Undef) {
        cerr << "Error: " << msg;
        return 1;
    }
    SRef bsr = logic.getSort_bool();

    // First arg is the return sort
    PTRef a_tr = logic.mkConst(sr, "a");
    PTRef b_tr = logic.mkConst(sr, "b");
    PTRef c_tr = logic.mkConst(sr, "c");

    vec<SRef> sort_args_f;
    sort_args_f.push(sr);
    sort_args_f.push(sr);

    SymRef sym_f = logic.declareFun("f", sr, sort_args_f, &msg);
    assert(sym_f != SymRef_Undef);

    vec<PTRef> f_args;
    f_args.push(a_tr);
    f_args.push(b_tr);

    PTRef f_a_b_tr = logic.mkFun(sym_f, f_args, &msg);

    assert(f_a_b_tr != PTRef_Undef);

    // eq_1 : (= (f a b) a)
    vec<PTRef> eq_args;
    eq_args.push(f_a_b_tr);
    eq_args.push(a_tr);

    PTRef eq_1 = logic.mkEq(eq_args);
    assert(logic.isEquality(eq_1));
    vec<PtPair> ites;
    vec<PTRef> nested_bools;
    egraph.declareTermTree(eq_1);

    // (f (f a b) b)
    vec<PTRef> f_f_args;
    f_f_args.push(f_a_b_tr);
    f_f_args.push(b_tr);
    PTRef f_f_a_b_tr = logic.mkFun(sym_f, f_f_args, &msg);
    assert (f_f_a_b_tr != PTRef_Undef);

    // eq_2 : (= (f (f a b) b) b)
    vec<PTRef> eq_args_2;
    eq_args_2.push(f_f_a_b_tr);
    eq_args_2.push(b_tr);
    PTRef eq_2 = logic.mkEq(eq_args_2);
    egraph.declareTermTree(eq_2);

    // eq_3 : (= (f (f a b) b) c)
    vec<PTRef> eq_args_3;
    eq_args_3.push(f_f_a_b_tr);
    eq_args_3.push(c_tr);
    PTRef eq_3 = logic.mkEq(eq_args_3);
    egraph.declareTermTree(eq_3);

    // eq_4 : (= a c)
    vec<PTRef> eq_args_4;
    eq_args_4.push(a_tr);
    eq_args_4.push(c_tr);
    PTRef eq_4 = logic.mkEq(eq_args_4);
    egraph.declareTermTree(eq_4);

    // Assert the stuff

    lbool rval = egraph.addEquality(PtAsgn(eq_1, l_True));
    assert(rval == l_Undef);
    rval = egraph.addTrue(eq_1) == true ? l_Undef : l_False;
    assert(rval == l_Undef);

    rval = egraph.addEquality(PtAsgn(eq_2, l_True));
    assert(rval == l_Undef);
    rval = egraph.addTrue(eq_2) == true ? l_Undef : l_False;
    assert(rval == l_Undef);

    rval = egraph.addEquality(PtAsgn(eq_3, l_True));
    assert(rval == l_Undef);
    rval = egraph.addTrue(eq_3) == true ? l_Undef : l_False;
    assert(rval == l_Undef);

    printf("%s\n", egraph.printEqClass(a_tr));
    printf("%s\n", egraph.printEqClass(logic.getTerm_true()));
    printf("%s\n", egraph.printEqClass(logic.getTerm_false()));

    while (true) {
        PtAsgn_reason& e = egraph.getDeduction();
        if (e.tr == PTRef_Undef) break;
        cout << logic.printTerm(e.tr) << endl;
    }
    rval = egraph.addDisequality(PtAsgn(eq_4, l_False));
    assert(rval == l_False);


    return 0;
}
