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
    PtStore term_store(sym_store, sort_store, logic.getSym_true, logic.getSym_false);

    Identifier i("TSort");

    ERef er = estore.addSymb(TRef_Undef);
    estore.addTerm(er);
    return 0;
}
