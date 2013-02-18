#include "Sort.h"
#include "SStore.h"
#include "TStore.h"
#include "Term.h"
#include "PtStore.h"
#include "Pterm.h"
#include "Logic.h"
#include "Enode.h"
#include "EnodeStore.h"
#include "Egraph.h"

int main(int argc, char **argv) {
    SMTConfig cfg(argc, argv);
//    EnodeStore estore;
    SStore sort_store(cfg);
    TStore sym_store;
    PtStore term_store(sym_store, sort_store);
    Logic logic(cfg, sort_store, sym_store, term_store);
    Egraph egraph(cfg, sort_store, sym_store, term_store, logic);

    Identifier i("TSort");
    Sort s(i);
    sort_store.insertStore(&s);
    logic.declare_sort_hook(&s);
    vec<SRef> sort_args_a;
    SRef sr = sort_store["TSort 0"];
    SRef bsr = sort_store["Bool 0"];
    sort_args_a.push(sr);
    // First arg is the return sort
    TRef a_tr = sym_store.newTerm("a", sort_args_a);
    TRef b_tr = sym_store.newTerm("b", sort_args_a);
    TRef c_tr = sym_store.newTerm("c", sort_args_a);

    vec<SRef> sort_args_f;
    sort_args_f.push(sort_store["TSort 0"]);
    sort_args_f.push(sort_store["TSort 0"]);
    sort_args_f.push(sort_store["TSort 0"]);
    TRef f_tr = sym_store.newTerm("f", sort_args_f);

    vec<TRef>& eq_syms = sym_store.nameToRef("=");
    TRef eq_sym = TRef_Undef;  // Find the equality symbol for the equality of TSort 0
    for (int i = 0; i < eq_syms.size(); i++) {
        Term& sym = sym_store[eq_syms[i]];
        if (sym[0] == sr && sym[1] == sr) {
            eq_sym = eq_syms[i];
            break;
        }
    }

    vec<TRef>& not_syms = sym_store.nameToRef("not");
    TRef not_sym = TRef_Undef;
    for (int i = 0; i < not_syms.size(); i++) {
        Term& sym = sym_store[not_syms[i]];
        if (sym[0] == bsr) {
            not_sym = not_syms[i];
            break;
        }
    }

    assert(eq_sym != TRef_Undef);
    assert(not_sym != TRef_Undef);

    // Add the terms
    // a
    PTRef a_ptr = term_store.insertTerm(a_tr, vec<PTRef>());
    // b
    PTRef b_ptr = term_store.insertTerm(b_tr, vec<PTRef>());
    // c
    PTRef c_ptr = term_store.insertTerm(c_tr, vec<PTRef>());
    // f a b
    vec<PTRef> f_args;
    f_args.push(a_ptr);
    f_args.push(b_ptr);
    PTRef f_a_b_ptr = term_store.insertTerm(f_tr, f_args);
    // = (f a b) a
    vec<PTRef> eq_args;
    eq_args.push(f_a_b_ptr);
    eq_args.push(a_ptr);
    PTRef eq_ptr = term_store.insertTerm(eq_sym, eq_args);

    // f (f a b) b
    vec<PTRef> f2_args;
    f2_args.push(f_a_b_ptr);
    f2_args.push(b_ptr);
    PTRef f2_f_a_b_b_ptr = term_store.insertTerm(f_tr, f2_args);

    // = (f (f a b) b) c
    vec<PTRef> eq2_args;
    eq2_args.push(f2_f_a_b_b_ptr);
    eq2_args.push(c_ptr);
    PTRef eq2_ptr = term_store.insertTerm(eq_sym, eq2_args);

    // = (a c)
    vec<PTRef> eq3_args;
    eq3_args.push(a_ptr);
    eq3_args.push(c_ptr);
    PTRef eq3_ptr = term_store.insertTerm(eq_sym, eq3_args);
    // not (= (a c))
    vec<PTRef> deq_args;
    deq_args.push(eq3_ptr);
    PTRef deq_ptr = term_store.insertTerm(not_sym, deq_args);

    lbool rval = egraph.addEquality(eq3_ptr, false);
    assert(rval == l_Undef);

    rval = egraph.addEquality(eq2_ptr, true);
    assert(rval == l_Undef);

    rval = egraph.addEquality(eq_ptr, true);
    assert(rval == l_False);

    // Symbols
//    ERef a_er = estore.addSymb(a_tr);
//    ERef b_er = estore.addSymb(b_tr);
//    ERef c_er = estore.addSymb(c_tr);
//    ERef f_er = estore.addSymb(f_tr);
//
//    ERef ERef_Nil = estore.get_Nil();
//
//    // Enode Terms
//    ERef a = estore.addTerm(a_er, ERef_Nil, a_ptr);
//    ERef b = estore.addTerm(b_er, ERef_Nil, b_ptr);
//    ERef c = estore.addTerm(c_er, ERef_Nil, c_ptr);
//
//    // Enode Lists
//    ERef b_list_er = estore.cons(b, estore.get_Nil());
//    ERef a_b_list_er = estore.cons(a, b_list_er);
//
//    // f(a,b) term
//    ERef f_a_b = estore.addTerm(f_er, a_b_list_er, f_a_b_ptr);
//
//    // Enode Lists continue
//    ERef f2_arg_list_er = estore.cons(f_a_b, b_list_er);
//
//    // Enode Terms continue
//    ERef f2_a_b_b = estore.addTerm(f_er, f2_arg_list_er, f2_f_a_b_b_ptr);
//
//    // a != c
//    bool rval = egraph.assertNEq(a, c, deq_ptr);
//    assert(rval == true);
//    // f(f(a,b),b) = c
//    rval = egraph.assertEq(f2_a_b_b, c, eq2_ptr);
//    assert(rval == true);
//    // f(a,b) = a
//    rval = egraph.assertEq(f_a_b, a, eq_ptr);
//    assert(rval == false);
//
    return 0;
}
