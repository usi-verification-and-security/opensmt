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
    //PTRef ab_neg = logic.mkCUFNeg(ab);

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
    stat = bbb.insert(eq, output);
    if (stat == l_True)
        printf("sat after eq\n");
    if (stat == l_False)
        printf("unsat after eq\n");

    BVRef output2;
    stat = bbb.insert(eq_neg, output2);
    if (stat == l_True)
        printf("sat after eq_neg\n");
    if (stat == l_False)
        printf("unsat after eq_neg\n");


    PTRef uf1 = logic.mkCUFVar("uf1");
    PTRef uf2 = logic.mkCUFVar("uf2");
    stat = bbb.glueUFtoB(uf1, output);
    if (stat == l_True)
        printf("sat after uf1\n");
    if (stat == l_False)
        printf("unsat after uf1\n");

    stat = bbb.glueBtoUF(output2, uf2);
    if (stat == l_True)
        printf("sat after uf2\n");
    if (stat == l_False)
        printf("unsat after uf2\n");

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
