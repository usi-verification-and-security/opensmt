#include <opensmt/opensmt2.h>
#include <opensmt/BitBlaster.h>
#include <stdio.h>

int
main(int argc, char** argv)
{

    if (argc != 3)
    {
        printf("Computes a / b\n");
        printf("Usage: %s <a> <b>\n", argv[0]);
        return 1;
    }
    int c1_int = atoi(argv[1]);
    int c2_int = atoi(argv[2]);
    SMTConfig c;
    CUFTheory cuftheory(c, 8);
    THandler thandler(c, cuftheory);
    SimpSMTSolver solver(c, thandler);
    MainSolver mainSolver(thandler, c, &solver);

    BVLogic& logic = cuftheory.getLogic();

    PTRef a = logic.mkBVNumVar("a");
    PTRef b = logic.mkBVNumVar("b");
    PTRef c1 = logic.mkBVConst(c1_int);
    PTRef c2 = logic.mkBVConst(c2_int);

    PTRef eq1 = logic.mkEq(a, c1);
    PTRef eq2 = logic.mkEq(b, c2);

    PTRef div = logic.mkBVDiv(a, b);
    PTRef d = logic.mkBVNumVar("d");

    PTRef eq3 = logic.mkEq(div, d);

    SolverId id = { 5 };
    vec<PtAsgn> asgns;
    vec<DedElem> deds;
    vec<PTRef> foo;

    BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);
    BVRef output;

    lbool stat;
    stat = bbb.insertEq(eq1, output);
    bbb.insertEq(eq2, output);
    bbb.insertEq(eq3, output);

    sstat r = mainSolver.check();

    if (r == s_True) {
        printf("sat\n");
        bbb.computeModel();
        ValPair v = bbb.getValue(d);
        printf("%s\n", v.val);

    }
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
