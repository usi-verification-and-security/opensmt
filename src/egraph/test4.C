/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
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
