/***************************************************
 * Created on: Jan 17, 2017
 * Author: Sepideh Asadi
 * d=a*b /\ a=2 /\ b=5 /\ d=1
 *
 * For values:
 *  a=0, b=5 , d=0 :  sat
 *  a=2, b=5 , d=11 :  unsat
 *  a=2, b=5 , d=10 :  sat
 *
 * Insert four Equalities with InsertEq()
 * we cannot have such not(d=10)
 ***************************************************/

#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>
//#include <opensmt/BVLogic.h>

int main(int argc, char** argv)
{
    BVLogic logic;
    SMTConfig c;
    MainSolver* mainSolver_ = new MainSolver(logic, c, "test solver");
    MainSolver& mainSolver = *mainSolver_;

    PTRef const1 = logic.mkBVConst(0);
    PTRef const2 = logic.mkBVConst(5);
    PTRef const3 = logic.mkBVConst(0);

    PTRef a = logic.mkBVNumVar("a");
    PTRef b = logic.mkBVNumVar("b");
    PTRef d = logic.mkBVNumVar("d");

    PTRef eq1 = logic.mkBVEq(a, const1);

    PTRef eq2 = logic.mkBVEq(b, const2);

    PTRef eq3 = logic.mkBVEq(d, const3);
    //PTRef eq3_neg = logic.mkNot(eq3);

    PTRef d2 = logic.mkBVTimes(a, b);
    PTRef eq4 = logic.mkBVEq(d, d2);
/******************************************************/
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
	stat = bbb.insertEq(eq4, output4);

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
