/************************************************
 * Created on: Jan 17, 2017
 * Author: Sepideh Asadi
 * a=1 /\ b=1 /\ d=0 /\ d=a & b
 ************************************************/

#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>


int
main(int argc, char** argv)
{
    BVLogic logic;
    SMTConfig c;
    MainSolver* mainSolver_ = new MainSolver(logic, c, "test solver");
    MainSolver& mainSolver = *mainSolver_;

    PTRef a = logic.mkBVNumVar("a");
    PTRef const1 = logic.mkBVConst(-1);
    PTRef eq1 = logic.mkBVEq(a, const1);

    PTRef b = logic.mkBVNumVar("b");
    PTRef const2 = logic.mkBVConst(4);
    PTRef eq2 = logic.mkBVEq(b, const2);

    PTRef d = logic.mkBVNumVar("d");
    PTRef const3 = logic.mkBVConst(4);
    PTRef eq3 = logic.mkBVEq(d, const3);
    //PTRef eq3_neg = logic.mkBVNot(eq3);

    PTRef d2 = logic.mkBVBwAnd(a, b);
    PTRef eq4 = logic.mkBVEq(d, d2);


   /* vec<PTRef> args;
    args.push(eq1);
    args.push(eq2);
    args.push(eq3_neg);
    args.push(eq4);

    PTRef eq = logic.mkAnd(args);*/

	vec<PtAsgn> asgns;
	vec<PTRef> foo;

	BitBlaster bbb({42}, c, mainSolver, logic, asgns, foo);

	BVRef output1;
	lbool stat;
	stat = bbb.insertEq(eq1, output1);
	if (stat == l_True)
		printf("sat after eq\n");
	if (stat == l_False)
		printf("unsat after eq\n");

	BVRef output2;
	stat = bbb.insertEq(eq2, output2);
//	if (stat == l_True)
//		printf("sat after eq_neg\n");
//	if (stat == l_False)
//		printf("unsat after eq_neg\n");

	BVRef output3;
	stat = bbb.insertEq(eq3, output3);
//	if (stat == l_True)
//		printf("sat after eq_neg\n");
//	if (stat == l_False)
//		printf("unsat after eq_neg\n");

	BVRef output4;
	stat = bbb.insertEq(eq4, output4);
//	if (stat == l_True)
//		printf("sat after eq_neg\n");
//	if (stat == l_False)
//		printf("unsat after eq_neg\n");

/****************************************************/
/*	PTRef uf1 = logic.mkCUFVar("uf1");
	PTRef uf2 = logic.mkCUFVar("uf2");

	stat = bbb.glueUFtoB(uf1, output);
	stat = bbb.glueBtoUF(output, uf1);
	if (stat == l_True)
		printf("sat after uf1\n");
	if (stat == l_False)
		printf("unsat after uf1\n");

	stat = bbb.glueUFtoB(uf2, output2);
	stat = bbb.glueBtoUF(output2, uf2);
	if (stat == l_True)
		printf("sat after uf2\n");
	if (stat == l_False)
		printf("unsat after uf2\n");

	PTRef uf_eq = logic.mkEq(uf1, uf2);
	char* msg;
	mainSolver.insertFormula(uf_eq, &msg);

    mainSolver.push(eq);*/

	std::cout << logic.printTerm(eq1) << "\n";
	std::cout << logic.printTerm(eq2) << "\n";
	std::cout << logic.printTerm(eq3) << "\n";
	std::cout << logic.printTerm(d2) << "\n";
	std::cout << logic.printTerm(eq4) << "\n";

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
