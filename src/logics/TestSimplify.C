#include "Sort.h"
#include "SStore.h"
#include "SymStore.h"
#include "Symbol.h"
#include "PtStore.h"
#include "Pterm.h"
#include "Logic.h"

int main(int argc, char** argv) {
    SMTConfig cfg(argc, argv);
    SStore sort_store(cfg);
    SymStore sym_store;
    PtStore term_store(sym_store, sort_store);
    Logic logic(cfg, sort_store, sym_store, term_store);

    assert(logic.setLogic("QF_UF"));
    SRef bsr = logic.getSort_bool();
    PTRef t1 = logic.mkConst(bsr, "t1");
    PTRef t2 = logic.mkConst(bsr, "t2");
    vec<PTRef> args1;
    args1.push(t1);
    args1.push(logic.getTerm_true());
    args1.push(t1);
    args1.push(t2);
    const char* msg;
    // No simplification
    cerr << "Term " << logic.getSym_and().x << " (" << sym_store.getName(logic.getSym_and()) << ")" << (sym_store[logic.getSym_and()].commutes() ? " commutes." : " does not commute.") << endl;
    PTRef and1 = logic.insertTerm(logic.getSym_and(), args1, &msg);

    vec<PTRef> args2;
    args2.push(t1);
    args2.push(t2);
    PTRef and2 = logic.insertTerm(logic.getSym_and(), args2, &msg);

    vec<PTRef> args3;
    args3.push(and1);
    args3.push(and1);
    args3.push(and2);
    PTRef or1 = logic.insertTerm(logic.getSym_or(), args3, &msg);

    Pterm& or1_t_old = logic.getPterm(or1);
    cout << "before: " << term_store.printTerm(or1, true) << endl;
    cout << " - old term num " << or1.x << endl;
    cout << " - old term size " << or1_t_old.size() << endl;
    cout << " - old term children " << endl;
    for (int i = 0; i < or1_t_old.size(); i++)
        cout << "    " << or1_t_old[i].x << endl;

    logic.simplifyTree(or1);
    Pterm& or1_t = logic.getPterm(or1);
    cout << " - new term num " << or1.x << endl;
    cout << " - new term size " << or1_t.size() << endl;
    cout << " - new term children " << endl;
    for (int i = 0; i < or1_t.size(); i++)
        cout << "    " << or1_t[i].x << endl;
    cerr << endl;
    cout << "after: " << logic.printTerm(or1) << endl;
    return 0;
}
