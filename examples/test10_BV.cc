/************************************************
 * Created on: Jan 25, 2017
 * (not (a=1) \/ b=3  )
 * result : sat
 ************************************************/
#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>

int main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory cuftheory(c);
    THandler thandler(c, cuftheory);
    SimpSMTSolver solver(c, thandler);
    MainSolver mainSolver(thandler, c, &solver);
    BVLogic& logic = cuftheory.getLogic();

    // BVLogic bvlogic(c);

    PTRef a = logic.mkBVNumVar("a");
    PTRef const1 = logic.mkBVConst(1);
    PTRef eq1 = logic.mkBVEq(a, const1);

    PTRef b = logic.mkBVNumVar("b");
    PTRef const2 = logic.mkBVConst(3);
    PTRef eq2 = logic.mkBVEq(b, const2);

    PTRef eq1_neg = logic.mkBVNot(eq1);
    PTRef LOr = logic.mkBVLor(eq1_neg, eq2);

    SolverId id = { 5 };
	vec<PtAsgn> asgns;
	vec<DedElem> deds;
	vec<PTRef> foo;

	BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);

	BVRef output1;
	lbool stat;
	stat = bbb.insertOr(LOr, output1);


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
