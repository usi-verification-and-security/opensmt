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
#include "Enode.h"
#include "EnodeStore.h"
#include "Egraph.h"
#include "TermMapper.h"
#include "GCTest.h"

GCTest::GCTest(int argc, char **argv) {
#ifdef CUSTOM_EL_ALLOC
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
    const char* msg;
    SymRef a_tr = sym_store.newSymb("a", sort_args_a, &msg);
    SymRef b_tr = sym_store.newSymb("b", sort_args_a, &msg);
    SymRef c_tr = sym_store.newSymb("c", sort_args_a, &msg);

    vec<SRef> sort_args_f;
    sort_args_f.push(sort_store["TSort 0"]);
    sort_args_f.push(sort_store["TSort 0"]);
    sort_args_f.push(sort_store["TSort 0"]);
    SymRef f_tr = sym_store.newSymb("f", sort_args_f, &msg);

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
    egraph.declareTermTree(eq2_ptr);

    egraph.declareTermTree(eq_ptr);

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
