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

    lbool res = logic.simplifyTree(or1);
    if (res == l_True) cout << "simplified to true" << endl;
    else if (res == l_False) cout << "simplified to false" << endl;
    else {
        Pterm& or1_t = logic.getPterm(or1);
        cout << " - new term num " << or1.x << endl;
        cout << " - new term size " << or1_t.size() << endl;
        cout << " - new term children " << endl;
        for (int i = 0; i < or1_t.size(); i++)
            cout << "    " << or1_t[i].x << endl;
        cerr << endl;
        cout << "after: " << logic.printTerm(or1) << endl;
    }
    return 0;
}
