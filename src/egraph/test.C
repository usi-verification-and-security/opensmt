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

    Identifier i("TSort");
    Sort s(i);
    sort_store.insertStore(&s);
    logic.declare_sort_hook(&s);
    vec<SRef> sort_args_a;
    SRef sr = sort_store["TSort 0"];
    SRef bsr = sort_store["Bool 0"];
    sort_args_a.push(sr);
    // First arg is the return sort
    SymRef a_tr = sym_store.newSymb("a", sort_args_a);
    SymRef b_tr = sym_store.newSymb("b", sort_args_a);
    SymRef c_tr = sym_store.newSymb("c", sort_args_a);

    vec<SRef> sort_args_f;
    sort_args_f.push(sort_store["TSort 0"]);
    sort_args_f.push(sort_store["TSort 0"]);
    sort_args_f.push(sort_store["TSort 0"]);
    SymRef f_tr = sym_store.newSymb("f", sort_args_f);

    vec<SymRef>& eq_syms = sym_store.nameToRef("=");
    SymRef eq_sym = SymRef_Undef;  // Find the equality symbol for the equality of TSort 0
    for (int i = 0; i < eq_syms.size(); i++) {
        Symbol& sym = sym_store[eq_syms[i]];
        if (sym[0] == sr && sym[1] == sr) {
            eq_sym = eq_syms[i];
            break;
        }
    }

    vec<SymRef>& not_syms = sym_store.nameToRef("not");
    SymRef not_sym = SymRef_Undef;
    for (int i = 0; i < not_syms.size(); i++) {
        Symbol& sym = sym_store[not_syms[i]];
        if (sym[0] == bsr) {
            not_sym = not_syms[i];
            break;
        }
    }

    assert(eq_sym != SymRef_Undef);
    assert(not_sym != SymRef_Undef);

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

    lbool rval = egraph.addEquality(eq3_ptr);
    assert(rval == l_Undef);

    rval = egraph.addDisequality(eq2_ptr);
    assert(rval == l_Undef);

    rval = egraph.addDisequality(eq_ptr);
    assert(rval == l_False);

    return 0;
}
