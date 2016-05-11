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
#include "GCTest.h"

GCTest::GCTest(int argc, char **argv) {
#ifdef CUSTOM_EL_ALLOC
    SMTConfig cfg(argc, argv);
    Logic logic(cfg);
    TermMapper tmap(logic);
    vec<DedElem> d;
    Egraph egraph(cfg, logic, tmap, d);

    char* msg;
    SRef sr = logic.declareSort("TSort", &msg);
    vec<SRef> sort_args_a;
    SRef bsr = logic.getSort_bool();
    sort_args_a.push(sr);
    // First arg is the return sort
    SymRef a_tr = logic.newSymb("a", sort_args_a, &msg);
    SymRef b_tr = logic.newSymb("b", sort_args_a, &msg);
    SymRef c_tr = logic.newSymb("c", sort_args_a, &msg);

    vec<SRef> sort_args_f;
    sort_args_f.push(logic.getSortRef("TSort 0"));
    sort_args_f.push(logic.getSortRef("TSort 0"));
    sort_args_f.push(logic.getSortRef("TSort 0"));
    SymRef f_tr = logic.newSymb("f", sort_args_f, &msg);

    vec<SymRef>& eq_syms = logic.symNameToRef("=");
    SymRef eq_sym = SymRef_Undef;  // Find the equality symbol for the equality of TSort 0
    for (int i = 0; i < eq_syms.size(); i++) {
        const Symbol& sym = logic.getSym(eq_syms[i]);
        if (sym[0] == sr && sym[1] == sr) {
            eq_sym = eq_syms[i];
            break;
        }
    }

    vec<SymRef>& not_syms = logic.symNameToRef("not");
    SymRef not_sym = SymRef_Undef;
    for (int i = 0; i < not_syms.size(); i++) {
        const Symbol& sym = logic.getSym(not_syms[i]);
        if (sym[0] == bsr) {
            not_sym = not_syms[i];
            break;
        }
    }

    assert(eq_sym != SymRef_Undef);
    assert(not_sym != SymRef_Undef);

    // Add the terms
    vec<PTRef> tmp;
    // a
    PTRef a_ptr = logic.insertTerm(a_tr, tmp, &msg);
    // b
    PTRef b_ptr = logic.insertTerm(b_tr, tmp, &msg);
    // c
    PTRef c_ptr = logic.insertTerm(c_tr, tmp, &msg);
    // f a b
    vec<PTRef> f_args;
    f_args.push(a_ptr);
    f_args.push(b_ptr);
    PTRef f_a_b_ptr = logic.insertTerm(f_tr, f_args, &msg);
    // = (f a b) a
    vec<PTRef> eq_args;
    eq_args.push(f_a_b_ptr);
    eq_args.push(a_ptr);
    PTRef eq_ptr = logic.insertTerm(eq_sym, eq_args, &msg);

    // f (f a b) b
    vec<PTRef> f2_args;
    f2_args.push(f_a_b_ptr);
    f2_args.push(b_ptr);
    PTRef f2_f_a_b_b_ptr = logic.insertTerm(f_tr, f2_args, &msg);

    // = (f (f a b) b) c
    vec<PTRef> eq2_args;
    eq2_args.push(f2_f_a_b_b_ptr);
    eq2_args.push(c_ptr);
    PTRef eq2_ptr = logic.insertTerm(eq_sym, eq2_args, &msg);

    // = (a c)
    vec<PTRef> eq3_args;
    eq3_args.push(a_ptr);
    eq3_args.push(c_ptr);
    PTRef eq3_ptr = logic.insertTerm(eq_sym, eq3_args, &msg);
    // not (= (a c))
    vec<PTRef> deq_args;
    deq_args.push(eq3_ptr);
    PTRef deq_ptr = logic.insertTerm(not_sym, deq_args, &msg);

    // add the terms
    vec<PtPair> v;
    vec<PTRef> dangling;
//    egraph.declareTermTree(eq2_ptr);

//    egraph.declareTermTree(eq_ptr);

    // Get their refs

    ERef er_a = egraph.enode_store.termToERef[a_ptr];
    ERef er_b = egraph.enode_store.termToERef[b_ptr];
    ERef er_c = egraph.enode_store.termToERef[c_ptr];
    ERef er_f = egraph.enode_store.termToERef[f_a_b_ptr];

    // not real reasons...
    ELRef dist_b = egraph.forbid_allocator.alloc(er_b, PtAsgn(eq_ptr, l_False), er_a);
    ELRef dist_c = egraph.forbid_allocator.alloc(er_c, PtAsgn(eq_ptr, l_False), ERef_Undef);
    ELRef dist_f = egraph.forbid_allocator.alloc(er_f, PtAsgn(eq_ptr, l_False), ERef_Undef);

    egraph.forbid_allocator[dist_b].link = dist_c;
    egraph.forbid_allocator[dist_c].link = dist_f;
    egraph.forbid_allocator[dist_f].link = dist_b;

    egraph.enode_store[er_a].setForbid(dist_b);

    egraph.faGarbageCollect();

/*
    lbool rval = egraph.addEquality(eq3_ptr);
    assert(rval == l_Undef);

    rval = egraph.addDisequality(eq2_ptr);
    assert(rval == l_Undef);

    rval = egraph.addDisequality(eq_ptr);
    assert(rval == l_False);
*/
#endif
}

int main(int argc, char** argv) {
#ifdef CUSTOM_GC_ALLOC
    GCTest t(argc, argv);
#endif
}
