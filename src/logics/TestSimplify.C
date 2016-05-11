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


#include "SSort.h"
#include "SStore.h"
#include "SymStore.h"
#include "Symbol.h"
#include "PtStore.h"
#include "Pterm.h"
#include "Logic.h"

int main(int argc, char** argv) {
    SMTConfig cfg(argc, argv);
    Logic logic(cfg);

    assert(logic.setLogic("QF_UF"));
    SRef bsr = logic.getSort_bool();
    PTRef t1 = logic.mkConst(bsr, "t1");
    PTRef t2 = logic.mkConst(bsr, "t2");
    vec<PTRef> args1;
    args1.push(t1);
    args1.push(logic.getTerm_true());
    args1.push(t1);
    args1.push(t2);
    char* msg;
    // No simplification
    cerr << "Term " << logic.getSym_and().x << " (" << logic.getSymName(logic.getSym_and()) << ")" << (logic.commutes(logic.getSym_and()) ? " commutes." : " does not commute.") << endl;
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
    cout << "before: " << logic.printTerm(or1, true) << endl;
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
