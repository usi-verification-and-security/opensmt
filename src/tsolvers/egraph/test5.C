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
#include "Enode.h"
#include "EnodeStore.h"
#include "Egraph.h"
#include "TermMapper.h"
#include "THandler.h"

int v = 0;

void setup(vec<DedElem>& deds, PTRef tr, TermMapper& tmap, Logic& l)
{
    printf("Setting up %s with var %d (deds length %d)\n", l.printTerm(tr), v, deds.size());
    deds.push(DedElem_Undef);
    tmap.addBinding(v++, tr);
}

int main(int argc, char **argv) {
    SMTConfig cfg(argc, argv);
    Logic logic(cfg);
    TermMapper tmap(logic);
    vec<DedElem> deds;
    THandler thandler(cfg, tmap, logic, deds);
//    Egraph egraph(cfg, logic, tmap, deds);

    bool l = logic.setLogic("QF_UF");
    assert(l);
    thandler.initializeTheorySolvers();

    char* msg;
    SRef sr = logic.declareSort("U", &msg);
    if (sr == SRef_Undef) {
        cerr << "Error: " << msg;
        return 1;
    }
    SRef bsr = logic.getSort_bool();
    // First arg is the return sort
    PTRef e4_tr = logic.mkVar(sr, "e4");
    PTRef e5_tr = logic.mkVar(sr, "e5");
    PTRef e2_tr = logic.mkVar(sr, "e2");

    // (op _ _)

    // First declare the function symbol op (U U) U
    vec<SRef> args;
    args.push(sr);
    args.push(sr);
    SymRef f = logic.declareFun("op", sr, args, &msg);
    assert(f != SymRef_Undef);

    // Then define the term (op e4 e4)
    vec<PTRef> targs;
    targs.push(e4_tr);
    targs.push(e4_tr);
    PTRef ope4e4_tr = logic.mkFun(f, targs, &msg);
    assert(ope4e4_tr != PTRef_Undef);

    // (op e4 e5)
    targs.clear();
    targs.push(e4_tr);
    targs.push(e5_tr);
    PTRef ope4e5_tr = logic.mkFun(f, targs, &msg);
    assert(ope4e5_tr != PTRef_Undef);


    // (op e5 e2)
    targs.clear();
    targs.push(e5_tr);
    targs.push(e2_tr);
    PTRef ope5e2_tr = logic.mkFun(f, targs, &msg);
    assert(ope5e2_tr != PTRef_Undef);

    // (op e5 e5)
    targs.clear();
    targs.push(e5_tr);
    targs.push(e5_tr);
    PTRef ope5e5_tr = logic.mkFun(f, targs, &msg);
    assert(ope5e5_tr != PTRef_Undef);

    // (op (op e4 e4) (op e4 e4))
    targs.clear();
    targs.push(ope4e4_tr);
    targs.push(ope4e4_tr);
    PTRef opope4e4ope4e4_tr = logic.mkFun(f, targs, &msg);
    assert(opope4e4ope4e4_tr != PTRef_Undef);

    // (op (op e4 e5) e4)
    targs.clear();
    targs.push(ope4e5_tr);
    targs.push(e4_tr);
    PTRef opope4e5e4_tr = logic.mkFun(f, targs, &msg);
    assert(opope4e5e4_tr != PTRef_Undef);

    // (op (op e5 e2) e5)
    targs.clear();
    targs.push(ope5e2_tr);
    targs.push(e5_tr);
    PTRef opope5e2e5_tr = logic.mkFun(f, targs, &msg);
    assert(opope5e2e5_tr != PTRef_Undef);

    // ===================================================
    // Equalities
    // ===================================================

    vec<PTRef> eq_args;

    // (= e5 (op e4 e4))
    eq_args.clear();
    eq_args.push(e5_tr);
    eq_args.push(ope4e4_tr);
    PTRef eq_e5_ope4e4_tr = logic.mkEq(eq_args);

    // (= e4 (op (op e4 e4) (op e4 e4)))
    eq_args.clear();
    eq_args.push(e4_tr);
    eq_args.push(opope4e4ope4e4_tr);
    PTRef eq_e4_opope4e4ope4e4_tr = logic.mkEq(eq_args);

    // (= e4 (op e5 e5))
    eq_args.clear();
    eq_args.push(e4_tr);
    eq_args.push(ope5e5_tr);
    PTRef eq_e4_ope5e5_tr = logic.mkEq(eq_args);

    // (= e4 (op e5 e2))
    eq_args.clear();
    eq_args.push(e4_tr);
    eq_args.push(ope5e2_tr);
    PTRef eq_e4_ope5e2_tr = logic.mkEq(eq_args);

    // (= (op e5 e2) (op e5 e5))
    eq_args.clear();
    eq_args.push(ope5e2_tr);
    eq_args.push(ope5e5_tr);
    PTRef eq_ope5e2_ope5e5_tr = logic.mkEq(eq_args);

    // (= e4 (op e4 e4))
    eq_args.clear();
    eq_args.push(e4_tr);
    eq_args.push(ope4e4_tr);
    PTRef eq_e4_ope4e4_tr = logic.mkEq(eq_args);

    // (= (op e4 e5) (op (op e4 e5) e4))
    eq_args.clear();
    eq_args.push(ope4e5_tr);
    eq_args.push(opope4e5e4_tr);
    PTRef eq_ope4e5_opope4e5e4_tr = logic.mkEq(eq_args);

    // (= (op e5 e2) (op (op e5 e2) e5))
    eq_args.clear();
    eq_args.push(ope5e2_tr);
    eq_args.push(opope5e2e5_tr);
    PTRef eq_ope5e2_opope5e2e5_tr = logic.mkEq(eq_args);

    // ===================================================
    // Declarations to thandler and setting up the var mapping (needed for
    // deductions)
    // ===================================================

    setup(deds, logic.getTerm_true(), tmap, logic);
    setup(deds, logic.getTerm_false(), tmap, logic);
    setup(deds, eq_e5_ope4e4_tr, tmap, logic);
    setup(deds, eq_e4_opope4e4ope4e4_tr, tmap, logic);
    setup(deds, eq_e4_ope5e5_tr, tmap, logic);
    setup(deds, eq_e4_ope5e2_tr, tmap, logic);
    setup(deds, eq_e4_ope4e4_tr , tmap, logic);
    setup(deds, eq_ope4e5_opope4e5e4_tr, tmap, logic);
    setup(deds, eq_ope5e2_opope5e2e5_tr, tmap, logic);
    setup(deds, eq_ope5e2_ope5e5_tr, tmap, logic);

    PTRef d = eq_e5_ope4e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    thandler.declareTermTree(d);
    d = eq_e4_opope4e4ope4e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    thandler.declareTermTree(d);
    d = eq_e4_ope5e5_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    thandler.declareTermTree(d);
    d = eq_e5_ope4e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    thandler.declareTermTree(d);
    d = eq_e4_ope5e2_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    thandler.declareTermTree(d);
    d = eq_ope5e2_ope5e5_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    thandler.declareTermTree(d);
    d = eq_e4_ope4e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    thandler.declareTermTree(d);
    d = eq_ope4e5_opope4e5e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    thandler.declareTermTree(d);
    d = eq_ope5e2_opope5e2e5_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    thandler.declareTermTree(d);

    vec<int> level;
    int dlev = 0;
    for (int i = 0; i < v; i++)
        level.push(dlev); // Init the dec levels

    // Assert the stuff
    bool rval;

    // Phase 1
    // not (= e4 (op e4 e4))

    d = eq_e4_ope4e4_tr;
    cerr << "Asserting not " << logic.printTerm(d) << endl;
    level[logic.getPterm(d).getVar()] = dlev++;
    thandler.stack.push(d);
    rval = thandler.assertLit(PtAsgn(d, l_False));
    assert(rval == true);

    // (= e4 (op e5 e2))
    d = eq_e4_ope5e2_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    level[logic.getPterm(d).getVar()] = dlev++;
    thandler.stack.push(d);
    rval = thandler.assertLit(PtAsgn(d, l_True));
    assert(rval == true);

    // (= (op e4 e5) (op (op e4 e5) e4))
    d = eq_ope4e5_opope4e5e4_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    level[logic.getPterm(d).getVar()] = dlev++;
    thandler.stack.push(d);
    rval = thandler.assertLit(PtAsgn(d, l_True));
    assert(rval == true);

    // (= (op e5 e2) (op (op e5 e2) e5))
    d = eq_ope5e2_opope5e2e5_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    level[logic.getPterm(d).getVar()] = dlev++;
    thandler.stack.push(d);
    rval = thandler.assertLit(PtAsgn(d, l_True));
    assert(rval == false);

    vec<Lit> cnfl;
    int max_dec_level;
    thandler.getConflict(cnfl, level, max_dec_level);

    cerr << "I'm now on dec level " << dlev << endl;
    dlev = -1;
    cerr << "Explanation:" << endl;
    for (int i = 0; i < cnfl.size(); i++) {
        cerr << " " << (lbool(sign(cnfl[i])) == l_True ? "not " : "") << logic.printTerm(tmap.varToPTRef(var(cnfl[i]))) << endl;
        if (level[var(cnfl[i])] > dlev) dlev = level[var(cnfl[i])]; // Update the level
    }
    cerr << "Now going to dec level " << dlev << endl;
    thandler.backtrack(dlev);

    d = eq_ope5e2_opope5e2e5_tr;
    cerr << "Asserting not " << logic.printTerm(d) << endl;
    level[logic.getPterm(d).getVar()] = dlev++;
    rval = thandler.assertLit(PtAsgn(d, l_False));
    assert(rval == true);

    // Phase 2
    cnfl.clear();

    d = eq_ope5e2_ope5e5_tr;
    cerr << "Asserting not " << logic.printTerm(d) << endl;
    level[logic.getPterm(d).getVar()] = dlev++;
    thandler.stack.push(d);
    rval = thandler.assertLit(PtAsgn(d, l_False));
    assert(rval == true);

    d = eq_e4_opope4e4ope4e4_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    level[logic.getPterm(d).getVar()] = dlev++;
    thandler.stack.push(d);
    rval = thandler.assertLit(PtAsgn(d, l_True));
    assert(rval == true);

    d = eq_e4_ope5e5_tr;
    cerr << "Asserting not " << logic.printTerm(d) << endl;
    level[logic.getPterm(d).getVar()] = dlev++;
    thandler.stack.push(d);
    rval = thandler.assertLit(PtAsgn(d, l_False));
    assert(rval == true);

    d = eq_e5_ope4e4_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    level[logic.getPterm(d).getVar()] = dlev++;
    thandler.stack.push(d);
    rval = thandler.assertLit(PtAsgn(d, l_True));
    assert(rval == false);

    thandler.getConflict(cnfl, level, max_dec_level);
    cerr << "Explanation:" << endl;
    for (int i = 0; i < cnfl.size(); i++) {
        cerr << " " << (lbool(sign(cnfl[i])) == l_True ? "not " : "") << logic.printTerm(tmap.varToPTRef(var(cnfl[i]))) << endl;
        cerr << thandler.printExplanation(tmap.varToPTRef(var(cnfl[i])));
    }

//    while (true) {
//        PtAsgn_reason& r = egraph.getDeduction();
//
//        if (r.tr == PTRef_Undef) { printf("No deductions\n"); break; }
//        else 
//            printf("Deduced term %s%s\n", r.sgn == l_True ? "" : "not ", logic.printTerm(r.tr));
//    }
//
    cerr << endl;
    printf("%s\n", thandler.printValue(logic.getTerm_true()));
    printf("%s\n", thandler.printValue(logic.getTerm_false()));
    return 0;
}
