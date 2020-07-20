/************************************************
 * Created on: Jan 30, 2017
 *  unsigned  f=g;                 >>eq1
    unsigned d = e*( f % 2 );       >>eq2
    unsigned d_p = e*( g % 2);      >>eq3
    assert(d == d_p);              >> (d != d_p ) = 1
}
 ************************************************/
#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>

int main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory* cuftheory = new CUFTheory(c);
    MainSolver* mainSolver_ = new MainSolver(std::unique_ptr<Theory>(cuftheory), c, "test solver");
    MainSolver& mainSolver = *mainSolver_;
    BVLogic& logic = cuftheory->getLogic();

    PTRef const1 = logic.mkBVConst(2);


    PTRef f = logic.mkBVNumVar("f");
    PTRef g = logic.mkBVNumVar("g");
    PTRef d = logic.mkBVNumVar("d");
    PTRef d_p = logic.mkBVNumVar("d_p");
    PTRef e = logic.mkBVNumVar("e");

    PTRef eq1 = logic.mkBVEq(f, g);

    PTRef mod1 = logic.mkBVMod(f, const1);
    PTRef mod2 = logic.mkBVMod(g, const1);

    PTRef mul1 = logic.mkBVTimes(mod1, e );
    PTRef mul2 = logic.mkBVTimes(mod2, e );

    PTRef eq2 = logic.mkBVEq(mul1, d);
    PTRef eq3 = logic.mkBVEq(mul2, d_p);

	PTRef eq_not = logic.mkBVNeq(d, d_p);

    PTRef constOne = logic.getTerm_BVOne();

    PTRef assert = logic.mkBVEq(constOne, eq_not);

	vec<PtAsgn> asgns;
	vec<PTRef> foo;

    SolverId id = {42};
	BitBlaster bbb(id, c, mainSolver, logic, asgns, foo);

	BVRef output1;
	lbool stat;
	stat = bbb.insertEq(eq1, output1);

	BVRef output2;
	stat = bbb.insertEq(eq2, output2);

	BVRef output3;
	stat = bbb.insertEq(eq3, output3);

	BVRef output4;
	stat = bbb.insertEq(assert, output4);

	std::cout << logic.printTerm(eq1) << "\n";
	std::cout << logic.printTerm(eq2) << "\n";
	std::cout << logic.printTerm(eq3) << "\n";
	std::cout << logic.printTerm(assert) << "\n";


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
