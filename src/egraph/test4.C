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
    vec<SRef> args;
    args.push(sr);
    args.push(sr);
    SymRef f = logic.declareFun("op", sr, args, &msg);
    assert(f != SymRef_Undef);
    vec<PTRef> targs;
    targs.push(e0_tr);
    targs.push(e0_tr);
    PTRef ope0e0_tr = logic.mkFun(f, targs, &msg);
    assert(ope0e0_tr != PTRef_Undef);
    // eq_1 : (= e0 e1)
    vec<PTRef> eq_args;
    eq_args.push(e0_tr);
    eq_args.push(e1_tr);

    PTRef eq_e0_e1_tr = logic.mkEq(eq_args);

    // (= (= op e0 e0) e1)
    eq_args.clear();
    eq_args.push(ope0e0_tr);
    eq_args.push(e1_tr);
    PTRef eq_ope0e0_e1_tr = logic.mkEq(eq_args);

    eq_args.clear();
    eq_args.push(ope0e0_tr);
    eq_args.push(e2_tr);
    PTRef eq_ope0e0_e2_tr = logic.mkEq(eq_args);

    // declare equalities (= (op e0 e0) e2)
    //                    (= e0 e1)
    // and                (= (op e0 e0) e1)
    egraph.declareTermTree(eq_ope0e0_e2_tr);
    egraph.declareTermTree(eq_e0_e1_tr);
    egraph.declareTermTree(eq_ope0e0_e1_tr);

    // (= e0 e2)
    eq_args.clear();
    eq_args.push(e0_tr);
    eq_args.push(e2_tr);
    PTRef eq_e0e2_tr = logic.mkEq(eq_args);
    egraph.declareTermTree(eq_e0e2_tr);

    // (= e1 e2)
    eq_args.clear();
    eq_args.push(e1_tr);
    eq_args.push(e2_tr);
    PTRef eq_e1e2_tr = logic.mkEq(eq_args);
    egraph.declareTermTree(eq_e1e2_tr);

    // Assert the stuff

    lbool rval;
    rval = egraph.addDisequality(PtAsgn(eq_e1e2_tr, l_False));
    assert(rval == l_Undef);

    rval = egraph.addEquality(PtAsgn(eq_ope0e0_e1_tr, l_True));
    assert(rval == l_Undef);

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
