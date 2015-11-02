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
#include "THandler.h"

int v = 0;

void setup(vec<DedElem>& deds, PTRef tr, TermMapper& tmap, Logic& l)
{
    deds.push(DedElem_Undef);
    tmap.addBinding(v++, tr);
}

int main(int argc, char **argv) {
    SMTConfig cfg(argc, argv);
    Logic logic(cfg);
    TermMapper tmap(logic);
    vec<DedElem> d;
    THandler thandler(cfg, tmap, logic, d);

    assert(logic.setLogic("QF_UF"));
    thandler.initializeTheorySolvers();

    char* msg;
    SRef sr = logic.declareSort("U", &msg);
    if (sr == SRef_Undef) {
        cerr << "Error: " << msg;
        return 1;
    }
    SRef bsr = logic.getSort_bool();
    // First arg is the return sort
    PTRef e0_tr = logic.mkVar(sr, "e0");
    PTRef e1_tr = logic.mkVar(sr, "e1");
    PTRef e2_tr = logic.mkVar(sr, "e2");

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
    thandler.declareTermTree(eq_ope0e0_e2_tr);
    cerr << "declaring term " << logic.printTerm(eq_ope0e0_e1_tr) << endl;
    thandler.declareTermTree(eq_ope0e0_e1_tr);
    cerr << "declaring term " << logic.printTerm(eq_e1e2_tr) << endl;
    thandler.declareTermTree(eq_e1e2_tr);
//    cerr << "declaring term " << logic.printTerm(eq_e1e3_tr) << endl;
//    egraph.declareTermTree(eq_e1e3_tr);

    setup(d, logic.getTerm_true(), tmap, logic);
    setup(d, logic.getTerm_false(), tmap, logic);
    setup(d, eq_ope0e0_e1_tr, tmap, logic);
    setup(d, eq_e1e2_tr, tmap, logic);
    setup(d, eq_ope0e0_e2_tr, tmap, logic);

    // Assert the stuff

    bool rval;

    cerr << "Asserting " << logic.printTerm(eq_ope0e0_e1_tr) << endl;

    rval = thandler.assertLit(PtAsgn(eq_ope0e0_e1_tr, l_True));
    assert(rval == true);

    cerr << "Asserting not " << logic.printTerm(eq_e1e2_tr) << endl;
    rval = thandler.assertLit(PtAsgn(eq_e1e2_tr, l_False));
    assert(rval == true);

//    cerr << "Asserting not " << logic.printTerm(eq_e1e3_tr) << endl;
//    rval = egraph.addDisequality(PtAsgn(eq_e1e3_tr, l_False));
//    assert(rval == l_Undef);

    while (true) {
        Lit l;
        Lit deduced = thandler.getDeduction(l);
        if (deduced == lit_Undef) { printf("No deductions\n"); break; }
        else {
            PTRef tr = tmap.varToPTRef(var(l));
            printf("Deduced term %s%s\n", lbool(sign(l)) == l_True ? "" : "not ", logic.printTerm(tr));
        }
    }

    printf("%s\n", thandler.printValue(logic.getTerm_true()));
    printf("%s\n", thandler.printValue(logic.getTerm_false()));
    printf("%s\n", thandler.printValue(e1_tr));
    printf("%s\n", thandler.printValue(e2_tr));
    printf("%s\n", thandler.printValue(ope0e0_tr));
    return 0;
}
