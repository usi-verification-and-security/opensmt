/************************************************
 * Created on: Jan 25, 2017
 * second formula
 * (a=5 \/ b=1) /\ ( not a \/ b=3 )
 *
 * For values:
 * sat
 ************************************************/
#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>

int main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory* cuftheory = new CUFTheory(c);
    THandler* thandler = new THandler(*cuftheory);
    SimpSMTSolver* solver = new SimpSMTSolver(c, *thandler);
    MainSolver* mainSolver_ = new MainSolver(*thandler, c, solver, "test solver");
    MainSolver& mainSolver = *mainSolver_;
    BVLogic& logic = cuftheory->getLogic();

    PTRef a = logic.mkBVNumVar("a");
    PTRef const1 = logic.mkBVConst(5);
    PTRef eq1 = logic.mkBVEq(a, const1);

    PTRef b = logic.mkBVNumVar("b");
    PTRef const2 = logic.mkBVConst(1);
    PTRef eq2 = logic.mkBVEq(b, const2);

    PTRef eq3 = logic.mkBVLor(eq1, eq2);

    PTRef a_neg = logic.mkBVNot(a);
    PTRef const4 = logic.mkBVConst(3);
    PTRef eq4 = logic.mkBVEq(b, const4);
    PTRef eq5 = logic.mkBVLor(a_neg, eq4);
    //PTRef eq4 = logic.mkBVEq(eq3, LOr);

	vec<PtAsgn> asgns;
	vec<DedElem> deds;
	vec<PTRef> foo;

    SolverId id = {42};
	BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);

	BVRef output1;
	lbool stat;
	stat = bbb.insertOr(eq3, output1);

	BVRef output2;
	stat = bbb.insertOr(eq5, output2);

//	BVRef output4;
//	stat = bbb.insertEq(eq4, output4);

	std::cout << logic.printTerm(eq3) << "\n";
	std::cout << logic.printTerm(eq5) << "\n";

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
