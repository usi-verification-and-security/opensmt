/***************************************************
 * Created on: Jan 17, 2017
 * Author: Sepideh Asadi
 * a=5 /\ b=2 /\ d=0 /\ d=a*b
 * we cannot have such not(d=10)
 ***************************************************/

#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>
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

    PTRef const1 = logic.mkConst(1);
    PTRef const2 = logic.mkConst(1);
    PTRef const3 = logic.mkConst(0);

    PTRef a = logic.mkNumVar("a");
    PTRef b = logic.mkNumVar("b");
    PTRef d = logic.mkNumVar("d");

    PTRef eq1 = logic.mkBVEq(a, const1);

    PTRef eq2 = logic.mkBVEq(b, const2);

    PTRef eq3 = logic.mkBVEq(d, const3);
    //PTRef eq3_neg = logic.mkNot(eq3);

    PTRef d2 = logic.mkBVTimes(a, b);
    PTRef eq4 = logic.mkBVEq(d, d2);
/******************************************************/
    SolverId id = { 5 };
	vec<PtAsgn> asgns;
	vec<DedElem> deds;
	vec<PTRef> foo;

	BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);

	BVRef output1;
	lbool stat;
	stat = bbb.insertEq(eq1, output1);
//	if (stat == l_True)
//		printf("sat after eq\n");
//	if (stat == l_False)
//		printf("unsat after eq\n");

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

/******************************************************/

 /*   vec<PTRef> args;
    args.push(eq1);
    args.push(eq2);
    args.push(eq3_neg);
    args.push(eq4);

    PTRef eq = logic.mkAnd(args);

    mainSolver.push(eq);*/

	std::cout << logic.printTerm(eq1) << "\n";
	std::cout << logic.printTerm(eq2) << "\n";
	std::cout << logic.printTerm(eq3) << "\n";
	//std::cout << logic.printTerm(eq3_neg) << "\n";
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
