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

int v= 0;

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

    bool b = logic.setLogic("QF_UF");
    assert(b);
    thandler.initializeTheorySolvers();

    IdRef idr = logic.newIdentifier("TSort");
    vec<SRef> tmp;
    SRef sr = logic.newSort(idr, "TSort", tmp);
    logic.declare_sort_hook(sr);
    sr = logic.getSortRef("TSort");
    SRef bsr = logic.getSort_bool();
    // First arg is the return sort
    PTRef c_2_tr = logic.mkVar(sr, "c_2");
    PTRef c_3_tr = logic.mkVar(sr, "c_3");
    PTRef c16_tr = logic.mkVar(sr, "c16");

    // eq_1 : (= c_2 c16)
    vec<PTRef> eq_args;
    eq_args.push(c_2_tr);
    eq_args.push(c16_tr);

    PTRef eq_1 = logic.mkEq(eq_args);
    assert(logic.isEquality(eq_1));
    vec<PtPair> ites;
    vec<PTRef> nested_bools;

    thandler.declareTermTree(eq_1);


    // eq_2 : (= c_3 c16)
    vec<PTRef> eq_args_2;
    eq_args_2.push(c_3_tr);
    eq_args_2.push(c16_tr);
    PTRef eq_2 = logic.mkEq(eq_args_2);

    thandler.declareTermTree(eq_2);

    // eq_3 : (= c_2 c_3)
    vec<PTRef> eq_args_3;
    eq_args_3.push(c_2_tr);
    eq_args_3.push(c_3_tr);
    PTRef eq_3 = logic.mkEq(eq_args_3);

    thandler.declareTermTree(eq_3);


    // Assert the stuff
    setup(d, logic.getTerm_true(), tmap, logic);
    setup(d, logic.getTerm_false(), tmap, logic);
    setup(d, eq_1, tmap, logic);
    setup(d, eq_2, tmap, logic);
    setup(d, eq_3, tmap, logic);

    bool rval;
    rval = thandler.assertLit(PtAsgn(eq_1, l_True));
//    rval = egraph.addDisequality(PtAsgn(eq_1, l_False));
    assert(rval == true);
//    rval = egraph.addFalse(eq_1);
//    assert(rval == l_Undef);

    rval = thandler.assertLit(PtAsgn(eq_2, l_True));
    assert(rval == true);
//    rval = egraph.addTrue(eq_2);
//    assert(rval == l_Undef);


    while (true) {
        Lit l;
        Lit deduced = thandler.getDeduction(l);
        if (deduced == lit_Undef) { printf("No deductions\n"); break; }
        else
            printf("Deduced term %s%s\n", lbool(sign(deduced)) == l_True ? "" : "not ", logic.printTerm(tmap.varToPTRef(var(l))));
    }

    printf("%s\n", thandler.printValue(logic.getTerm_true()));
    printf("%s\n", thandler.printValue(logic.getTerm_false()));


    return 0;
}
