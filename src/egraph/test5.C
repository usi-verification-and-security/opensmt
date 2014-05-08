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

    assert(logic.setLogic("QF_UF"));

    const char* msg;
    SRef sr = logic.declareSort("U", &msg);
    if (sr == SRef_Undef) {
        cerr << "Error: " << msg;
        return 1;
    }
    SRef bsr = logic.getSort_bool();
    // First arg is the return sort
    PTRef e4_tr = logic.mkConst(sr, "e4");
    PTRef e5_tr = logic.mkConst(sr, "e5");
    PTRef e2_tr = logic.mkConst(sr, "e2");

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
    // Declarations to egraph
    // ===================================================

    PTRef d = eq_e5_ope4e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    egraph.declareTermTree(d);
    d = eq_e4_opope4e4ope4e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    egraph.declareTermTree(d);
    d = eq_e4_ope5e5_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    egraph.declareTermTree(d);
    d = eq_e5_ope4e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    egraph.declareTermTree(d);
    d = eq_e4_ope5e2_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    egraph.declareTermTree(d);
    d = eq_ope5e2_ope5e5_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    egraph.declareTermTree(d);
    d = eq_e4_ope4e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    egraph.declareTermTree(d);
    d = eq_ope4e5_opope4e5e4_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    egraph.declareTermTree(d);
    d = eq_ope5e2_opope5e2e5_tr;
    cerr << "declaring term " << logic.printTerm(d) << endl;
    egraph.declareTermTree(d);


    // Assert the stuff
    lbool rval;

    // Phase 1
    // not (= e4 (op e4 e4))

    d = eq_e4_ope4e4_tr;
    cerr << "Asserting not " << logic.printTerm(d) << endl;
    egraph.setPolarity(d, l_False);
    rval = egraph.addDisequality(PtAsgn(d, l_False));
    assert(rval == l_Undef);
    egraph.pushBacktrackPoint();


    // (= e4 (op e5 e2))
    d = eq_e4_ope5e2_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    egraph.setPolarity(d, l_True);
    rval = egraph.addEquality(PtAsgn(d, l_True));
    assert(rval == l_Undef);
    egraph.pushBacktrackPoint();

    // (= (op e4 e5) (op (op e4 e5) e4))
    d = eq_ope4e5_opope4e5e4_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    egraph.setPolarity(d, l_True);
    rval = egraph.addEquality(PtAsgn(d, l_True));
    assert(rval == l_Undef);
    egraph.pushBacktrackPoint();

    // (= (op e5 e2) (op (op e5 e2) e5))
    d = eq_ope5e2_opope5e2e5_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    egraph.setPolarity(d, l_True);
    rval = egraph.addEquality(PtAsgn(d, l_True));
    assert(rval == l_False);

    vec<PtAsgn> cnfl;
    egraph.getConflict(false, cnfl);

    cerr << "Explanation:" << endl;
    for (int i = 0; i < cnfl.size(); i++)
        cerr << " " << (cnfl[i].sgn == l_True ? "not " : "") << logic.printTerm(cnfl[i].tr) << endl;

    egraph.popBacktrackPoint();

    d = eq_ope5e2_opope5e2e5_tr;
    cerr << "Asserting not " << logic.printTerm(d) << endl;
    egraph.setPolarity(d, l_False);
    rval = egraph.addDisequality(PtAsgn(d, l_False));
    assert(rval == l_Undef);

    // Phase 2
    cnfl.clear();

    d = eq_ope5e2_ope5e5_tr;
    cerr << "Asserting not " << logic.printTerm(d) << endl;
    egraph.setPolarity(d, l_False);
    rval = egraph.addDisequality(PtAsgn(d, l_False));
    assert(rval == l_Undef);
    egraph.pushBacktrackPoint();

    d = eq_e4_opope4e4ope4e4_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    egraph.setPolarity(d, l_True);
    rval = egraph.addEquality(PtAsgn(d, l_True));
    assert(rval == l_Undef);
    egraph.pushBacktrackPoint();

    d = eq_e4_ope5e5_tr;
    cerr << "Asserting not " << logic.printTerm(d) << endl;
    egraph.setPolarity(d, l_False);
    rval = egraph.addDisequality(PtAsgn(d, l_False));
    assert(rval == l_Undef);
    egraph.pushBacktrackPoint();

    d = eq_e5_ope4e4_tr;
    cerr << "Asserting " << logic.printTerm(d) << endl;
    egraph.setPolarity(d, l_True);
    rval = egraph.addEquality(PtAsgn(d, l_True));
    assert(rval == l_False);

    egraph.getConflict(false, cnfl);
    cerr << "Explanation:" << endl;
    for (int i = 0; i < cnfl.size(); i++) {
        cerr << " " << (cnfl[i].sgn == l_True ? "not " : "") << logic.printTerm(cnfl[i].tr) << endl;
        cerr << egraph.printExplanationTreeDotty(cnfl[i].tr);
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
    printf("%s\n", egraph.printEqClass(logic.getTerm_true()));
    printf("%s\n", egraph.printEqClass(logic.getTerm_false()));
    return 0;
}
