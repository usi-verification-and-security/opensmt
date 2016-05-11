#include <opensmt/opensmt2.h>
#include <stdio.h>

int
main(int argc, char** argv)
{
    SMTConfig c;
    UFTheory uftheory(c);
    THandler thandler(c, uftheory);
    SimpSMTSolver solver(c, thandler);
    MainSolver mainSolver(thandler, c, &solver);

    Logic& logic = thandler.getLogic();

    PTRef v = logic.mkBoolVar("a");
    PTRef v_neg = logic.mkNot(v);
    vec<PTRef> args;
    args.push(v);
    args.push(v_neg);
    PTRef a = logic.mkAnd(args);

    mainSolver.push(a);
    sstat r = mainSolver.check();

    if (r == s_True)
        printf("sat\n");
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknowon\n");
    else
        printf("error\n");

    return 0;
}
