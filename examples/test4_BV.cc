/************************************************
 * Created on: Jan 17, 2017
 * Author: Sepideh Asadi
 * a=36 /\ b=45 /\ not(d=54) /\ d=a && b
 ************************************************/

#include <opensmt/opensmt2.h>
#include <stdio.h>
//#include <opensmt/logic.h>


int
main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory cuftheory(c);
    THandler thandler(c, cuftheory);
    SimpSMTSolver solver(c, thandler);
    MainSolver mainSolver(thandler, c, &solver);
    BVLogic& logic = cuftheory.getLogic();

    // BVLogic bvlogic(c);

    PTRef a = logic.mkNumVar("a");
    PTRef thirtysix = logic.mkConst(36);
    PTRef eq1 = logic.mkEq(a, thirtysix);

    PTRef b = logic.mkNumVar("b");
    PTRef fortyfive = logic.mkConst(45);
    PTRef eq2 = logic.mkEq(a, fortyfive);

    PTRef d = logic.mkNumVar("d");
    PTRef fiftyfour = logic.mkConst(54);
    PTRef eq3 = logic.mkEq(a, fiftyfour);
    PTRef eq3_neg = logic.mkNot(eq3);

    PTRef d2 = logic.mkBVBwAnd(a, b);
    PTRef eq4 = logic.mkEq(d, d2);

    vec<PTRef> args;
    args.push(eq1);
    args.push(eq2);
    args.push(eq3_neg);
    args.push(eq4);

    PTRef eq = logic.mkAnd(args);

    mainSolver.push(eq);
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


