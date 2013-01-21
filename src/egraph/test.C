#include "Sort.h"
#include "SStore.h"
#include "TStore.h"
#include "Term.h"
#include "PtStore.h"
#include "Pterm.h"
#include "Logic.h"
#include "Enode.h"
#include "EnodeStore.h"

int main(int argc, char **argv) {
    SMTConfig cfg(argc, argv);
    EnodeStore estore;
    SStore sort_store(cfg);
    TStore sym_store;
    Logic logic(cfg, sort_store, sym_store);
    PtStore term_store(sym_store, sort_store, logic.getSym_true(), logic.getSym_false());

    Identifier i("TSort");
    Sort s(i);
    sort_store.insertStore(&s);
    vec<SRef> sort_args_a;
    sort_args_a.push(sort_store["TSort 0"]);
    // First arg is the return sort
    TRef a_tr = sym_store.newTerm("a", sort_args_a);
    TRef b_tr = sym_store.newTerm("b", sort_args_a);

    vec<SRef> sort_args_f;
    sort_args_f.push(sort_store["TSort 0"]);
    sort_args_f.push(sort_store["TSort 0"]);
    sort_args_f.push(sort_store["TSort 0"]);
    TRef f_tr = sym_store.newTerm("f", sort_args_f);

    // Symbols
    ERef a_er = estore.addSymb(a_tr);
    ERef b_er = estore.addSymb(b_tr);
    ERef f_er = estore.addSymb(f_tr);

    // Lists
    ERef b_list_er = estore.cons(b_er, estore.get_Nil());
    ERef a_b_list_er = estore.cons(a_er, b_list_er);
    ERef f_a_b = estore.cons(f_er, a_b_list_er);

    return 0;
}
