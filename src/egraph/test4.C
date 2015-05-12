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
    IdentifierStore id_store;
    SStore sort_store(cfg, id_store);
    SymStore sym_store;
    PtStore term_store(sym_store, sort_store);
    Logic logic(cfg, id_store, sort_store, sym_store, term_store);
    TermMapper tmap(logic);
    Egraph egraph(cfg, sort_store, sym_store, term_store, logic, tmap);

    assert(logic.setLogic("QF_UF"));

    char* msg;
    SRef sr = logic.declareSort("U", &msg);
    if (sr == SRef_Undef) {
        cerr << "Error: " << msg;
        return 1;
    }
    SRef bsr = logic.getSort_bool();
    // First arg is the return sort
    PTRef e0_tr = logic.mkConst(sr, "e0");
    PTRef e1_tr = logic.mkConst(sr, "e1");
    PTRef e2_tr = logic.mkConst(sr, "e2");

    // (op e0 e0)

    // First declare the function symbol op (U U) U
    vec<SRef> args;
    args.push(sr);
    args.push(sr);
    SymRef f = logic.declareFun("op", sr, args, &msg);
    assert(f != SymRef_Undef);

    // Then define the term (op e0 e0)
    vec<PTRef> targs;
    targs.push(e0_tr);
    targs.push(e0_tr);
    PTRef ope0e0_tr = logic.mkFun(f, targs, &msg);
    assert(ope0e0_tr != PTRef_Undef);

    vec<PTRef> eq_args;

    // (= (op e0 e0) e1)
    eq_args.clear();
    eq_args.push(ope0e0_tr);
    eq_args.push(e1_tr);
    PTRef eq_ope0e0_e1_tr = logic.mkEq(eq_args);

    // (= (op e0 e0) e2)
    eq_args.clear();
    eq_args.push(ope0e0_tr);
    eq_args.push(e2_tr);
    PTRef eq_ope0e0_e2_tr = logic.mkEq(eq_args);

    // (= e1 e2)
    eq_args.clear();
    eq_args.push(e1_tr);
    eq_args.push(e2_tr);
    PTRef eq_e1e2_tr = logic.mkEq(eq_args);
//    // (= e1 e3)
//    eq_args.clear();
//    eq_args.push(e1_tr);
//    eq_args.push(e3_tr);
//    PTRef eq_e1e3_tr = logic.mkEq(eq_args);

    // declare equalities (= (op e0 e0) e2)
    // and                (= (op e0 e0) e1)
    cerr << "declaring term " << logic.printTerm(eq_ope0e0_e2_tr) << endl;
    egraph.declareTermTree(eq_ope0e0_e2_tr);
    cerr << "declaring term " << logic.printTerm(eq_ope0e0_e1_tr) << endl;
    egraph.declareTermTree(eq_ope0e0_e1_tr);
    cerr << "declaring term " << logic.printTerm(eq_e1e2_tr) << endl;
    egraph.declareTermTree(eq_e1e2_tr);
//    cerr << "declaring term " << logic.printTerm(eq_e1e3_tr) << endl;
//    egraph.declareTermTree(eq_e1e3_tr);

    // Assert the stuff

    lbool rval;

    cerr << "Asserting " << logic.printTerm(eq_ope0e0_e1_tr) << endl;
    rval = egraph.addEquality(PtAsgn(eq_ope0e0_e1_tr, l_True));
    assert(rval == l_Undef);

    cerr << "Asserting not " << logic.printTerm(eq_e1e2_tr) << endl;
    rval = egraph.addDisequality(PtAsgn(eq_e1e2_tr, l_False));
    assert(rval == l_Undef);

//    cerr << "Asserting not " << logic.printTerm(eq_e1e3_tr) << endl;
//    rval = egraph.addDisequality(PtAsgn(eq_e1e3_tr, l_False));
//    assert(rval == l_Undef);

    while (true) {
        PtAsgn_reason& r = egraph.getDeduction();

        if (r.tr == PTRef_Undef) { printf("No deductions\n"); break; }
        else 
            printf("Deduced term %s%s\n", r.sgn == l_True ? "" : "not ", logic.printTerm(r.tr));
    }

    printf("%s\n", egraph.printEqClass(logic.getTerm_true()));
    printf("%s\n", egraph.printEqClass(logic.getTerm_false()));
    printf("%s\n", egraph.printEqClass(e1_tr));
    printf("%s\n", egraph.printEqClass(e2_tr));
    printf("%s\n", egraph.printDistinctions(e1_tr));
    printf("%s\n", egraph.printDistinctions(e2_tr));
    printf("%s\n", egraph.printDistinctions(ope0e0_tr));
    return 0;
}
