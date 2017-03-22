#include <opensmt/opensmt2.h>
#include <opensmt/BitBlaster.h>
#include <stdio.h>

int
main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory cuftheory(c);
    THandler thandler(c, cuftheory);
    SimpSMTSolver solver(c, thandler);
    MainSolver mainSolver(thandler, c, &solver);

    BVLogic& logic = cuftheory.getLogic();

    PTRef a = logic.mkNumVar("a");
    PTRef b = logic.mkNumVar("b");
    PTRef ab = logic.mkBVBwAnd(a, b);

    PTRef d = logic.mkNumVar("b");
    PTRef f = logic.mkNumVar("a");
    PTRef ba = logic.mkBVBwAnd(d, f);



    PTRef eq = logic.mkBVEq(ab,ba);
    PTRef eq_neg = logic.mkBVNot(eq);

    SolverId id = { 5 };
    vec<PtAsgn> asgns;
    vec<DedElem> deds;
    vec<PTRef> foo;

    BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);
    BVRef output;

    lbool stat;
    stat = bbb.insertEq(eq, output);
    if (stat == l_True)
        printf("sat after eq\n");
    if (stat == l_False)
        printf("unsat after eq\n");

//    BVRef output2;
//    stat = bbb.insert(eq_neg, output2);
//    if (stat == l_True)
//        printf("sat after eq_neg\n");
//    if (stat == l_False)
//        printf("unsat after eq_neg\n");


//    PTRef uf1 = logic.mkCUFVar("uf1");
//    PTRef uf2 = logic.mkCUFVar("uf2");
//    PTRef bv1 = logic.mkNumVar("bv1");
//    PTRef bv2 = logic.mkNumVar("bv2");
//    PTRef bv_eq1 = logic.mkBVEq(bv1, eq);
//    PTRef bv_eq2 = logic.mkBVEq(bv2, eq_neg);
//    PTRef bv_eq3 = logic.mkBVEq(bv1, bv2);
//
//    BVRef bvr1;
//    BVRef bvr2;
//    BVRef bvr3;
//
//    bbb.insertEq(bv_eq1, bvr1);
//    bbb.insertEq(bv_eq2, bvr2);
//    bbb.insertEq(bv_eq3, bvr3);
//
//
//    stat = bbb.glueUFtoB(uf1, bvr1);
//    stat = bbb.glueUFtoB(uf2, bvr2);
//
//    stat = bbb.glueUFtoUF(uf1, uf2);
//
//    PTRef uf_eq = logic.mkEq(uf1, uf2);
//    char* msg;
//    mainSolver.insertFormula(uf_eq, &msg);

    sstat r = mainSolver.check();

    if (r == s_True)
        printf("sat\n");
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
