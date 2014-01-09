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
    PTRef a_tr = logic.mkConst(sr, "a");
    PTRef b_tr = logic.mkConst(sr, "b");
    PTRef c_tr = logic.mkConst(sr, "c");

    vec<SRef> sort_args_f;
    sort_args_f.push(sr);
    sort_args_f.push(sr);
    sort_args_f.push(sr);

    SymRef sym_f = logic.newSymb("f", sort_args_f);
    assert(sym_f != SymRef_Undef);

    vec<PTRef> f_args;
    f_args.push(a_tr);
    f_args.push(b_tr);

    PTRef f_a_b_tr = logic.insertTerm(sym_f, f_args);

    assert(f_a_b_tr != PTRef_Undef);

    // eq_1 : (= (f a b) a)
    vec<PTRef> eq_args;
    eq_args.push(f_a_b_tr);
    eq_args.push(a_tr);

    PTRef eq_1 = logic.mkEq(eq_args);
    assert(logic.isEquality(eq_1));
    vec<PtPair> ites;
    vec<PTRef> nested_bools;
    egraph.addTerm(eq_1, ites, nested_bools);

    // (f (f a b) b)
    vec<PTRef> f_f_args;
    f_f_args.push(f_a_b_tr);
    f_f_args.push(b_tr);
    PTRef f_f_a_b_tr = logic.insertTerm(sym_f, f_f_args);

    // eq_2 : (= (f (f a b) b) b)
    vec<PTRef> eq_args_2;
    eq_args_2.push(f_f_a_b_tr);
    eq_args_2.push(b_tr);
    PTRef eq_2 = logic.mkEq(eq_args_2);
    egraph.addTerm(eq_2, ites, nested_bools);

    // eq_3 : (= (f (f a b) b) c)
    vec<PTRef> eq_args_3;
    eq_args_3.push(f_f_a_b_tr);
    eq_args_3.push(c_tr);
    PTRef eq_3 = logic.mkEq(eq_args_3);
    egraph.addTerm(eq_3, ites, nested_bools);

    // eq_4 : (= a c)
    vec<PTRef> eq_args_4;
    eq_args_4.push(a_tr);
    eq_args_4.push(c_tr);
    PTRef eq_4 = logic.mkEq(eq_args_4);
    egraph.addTerm(eq_4, ites, nested_bools);

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
