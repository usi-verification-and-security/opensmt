/************************************************
 * Created on: Jan 25, 2017 , Grisha's email example
 * ( (not a) \/ ( b = ( d + 1)))
 * in general(without value) it is sat
 *
 * For Values:
 * a=1 , b=1 , d=0   sat
 * a=7 , b=2 , d=1  sat
 * a=7 , b=2 , d=11  sat
 *
 * You are allowed only to use: InsertEq and InsertOr
 ************************************************/

#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>

int main()
{
    BVLogic logic{opensmt::Logic_t::QF_BV};
    SMTConfig c;
    MainSolver* mainSolver_ = new MainSolver(logic, c, "test solver");
    MainSolver& mainSolver = *mainSolver_;

    PTRef a = logic.mkBVNumVar("a");
    PTRef const1 = logic.mkBVConst(7);
    PTRef eq1 = logic.mkBVEq(a, const1);

    PTRef a_neg = logic.mkBVNot(a);

    PTRef b = logic.mkBVNumVar("b");
    PTRef const2 = logic.mkBVConst(2);
    PTRef eq2 = logic.mkBVEq(b, const2);

    PTRef d = logic.mkBVNumVar("d");
    PTRef const3 = logic.mkBVConst(11);
    PTRef eq3 = logic.mkBVEq(d, const3);

    PTRef one = logic.mkBVConst(1);
    PTRef dplusOne = logic.mkBVPlus(d, one);
    PTRef eq4 = logic.mkBVEq(b, dplusOne);

    PTRef eq5 = logic.mkBVLor(a_neg, eq4);

	vec<PtAsgn> asgns;
	vec<PTRef> foo;

    SolverId id = {42};
	BitBlaster bbb(id, c, mainSolver, logic, asgns, foo);

	BVRef output1;
	lbool stat;
	stat = bbb.insertOr(eq5 , output1);

	BVRef output2;
	stat = bbb.insertEq(eq1, output2);

	BVRef output3;
	stat = bbb.insertEq(eq2, output3);

	BVRef output4;
	stat = bbb.insertEq(eq3, output4);

//	std::cout << logic.printTerm(eq1) << "\n";
//	std::cout << logic.printTerm(eq2) << "\n";
//	std::cout << logic.printTerm(eq3) << "\n";
//	//std::cout << logic.printTerm(LOr) << "\n";
//	std::cout << logic.printTerm(eq4) << "\n";
//	std::cout << logic.printTerm(eq5) << "\n";


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
