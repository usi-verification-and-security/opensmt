/************************************************
 * Created on: Jan 30, 2017
 *  unsigned  f=g;
    unsigned d = ( f % 2 );
    unsigned d_p = ( g % 2);
    assert(d == d_p);
}
 ************************************************/
#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>

int main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory cuftheory(c , 8);
    THandler thandler(c, cuftheory);
    SimpSMTSolver solver(c, thandler);
    MainSolver mainSolver(thandler, c, &solver);
    BVLogic& logic = cuftheory.getLogic();

    PTRef const1 = logic.mkBVConst(-2);


    PTRef f = logic.mkBVNumVar("f");

    PTRef g = logic.mkBVNumVar("g");

    PTRef e = logic.mkBVNumVar("e");
    PTRef eq1 = logic.mkBVEq(f, g);


    PTRef mode1 = logic.mkBVMod(f, const1);
    PTRef mode2 = logic.mkBVMod(g, const1);

    PTRef mul1 = logic.mkBVTimes(mode1, e );
    PTRef mul2 = logic.mkBVTimes(mode2, e );
    PTRef eq2 = logic.mkBVEq(mul1, mul2);

    SolverId id = { 5 };
	vec<PtAsgn> asgns;
	vec<DedElem> deds;
	vec<PTRef> foo;

	BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);

	BVRef output1;
	lbool stat;
	stat = bbb.insertEq(eq1, output1);

	BVRef output2;
	stat = bbb.insertEq(eq2, output2);

	std::cout << logic.printTerm(eq1) << "\n";
	std::cout << logic.printTerm(eq2) << "\n";


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
