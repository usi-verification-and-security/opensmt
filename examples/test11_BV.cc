/************************************************
 * Created on: Jan 25, 2017
 * second formula
 * a=5 /\ b=1 /\ ( not a \/ b=3 )
 *
 * For values:
 * a=1, b=0, b=3 :   unsat
 * a=5, b=4, b=4 :   sat
 * a=1, b=1, b=1 :   sat
 ************************************************/
#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>

int main(int argc, char** argv)
{
    BVLogic logic{opensmt::Logic_t::QF_BV};
    SMTConfig c;
    MainSolver* mainSolver_ = new MainSolver(logic, c, "test solver");
    MainSolver& mainSolver = *mainSolver_;

    PTRef a = logic.mkBVNumVar("a");
    PTRef const1 = logic.mkBVConst(5);
    PTRef eq1 = logic.mkBVEq(a, const1);

    PTRef b = logic.mkBVNumVar("b");
    PTRef const2 = logic.mkBVConst(4);
    PTRef eq2 = logic.mkBVEq(b, const2);

    PTRef a_neg = logic.mkBVNot(a);
    PTRef const4 = logic.mkBVConst(4);
    PTRef eq4 = logic.mkBVEq(b, const4);
    PTRef LOr = logic.mkBVLor(a_neg, eq4);
    //PTRef eq4 = logic.mkBVEq(eq3, LOr);

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
	stat = bbb.insertOr(LOr, output3);

//	BVRef output4;
//	stat = bbb.insertEq(eq4, output4);

	std::cout << logic.printTerm(eq1) << "\n";
	std::cout << logic.printTerm(eq2) << "\n";
	std::cout << logic.printTerm(LOr) << "\n";
//	std::cout << logic.printTerm(LOr) << "\n";
//	std::cout << logic.printTerm(eq4) << "\n";

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
