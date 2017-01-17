/***************************************************
 * Created on: Jan 17, 2017
 * Author: Sepideh Asadi
 * a=5 /\ b=2 /\ not(d=10) /\ d=a*b
 ***************************************************/

#include <opensmt/opensmt2.h>
#include <stdio.h>
//#include <opensmt/BVLogic.h>


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

    PTRef five = logic.mkConst(5);
    PTRef two = logic.mkConst(2);
    PTRef ten = logic.mkConst(10);

    PTRef a = logic.mkNumVar("a");
    PTRef b = logic.mkNumVar("b");
    PTRef d = logic.mkNumVar("d");

    PTRef eq1 = logic.mkEq(a, five);
    PTRef eq2 = logic.mkEq(b, two);

    PTRef eq3 = logic.mkEq(d, ten);
    PTRef eq3_neg = logic.mkNot(eq3);

    PTRef d2 = logic.mkBVTimes(a, b);
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
