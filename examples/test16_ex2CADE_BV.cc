/************************************************
* Created on: Jan 30, 2017
unsigned a;
unsigned b;
unsigned c1 = (((a % 2) + (b % 2))) % 2;     //eq1
unsigned c2 = (a + b) % 2;					 //eq2
unsigned e, f;
e=g;
f=h;
unsigned d = e*f*c1;  						//eq3
unsigned d_p = g*h*c2;						//eq4
assert(d == d_p);                           //assert ((d != d_p ) = 1)
}
The result is UNSAT,means c1=c2 holds!

 ************************************************/
#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>

int main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory* cuftheory = new CUFTheory(c, 8);
    THandler* thandler = new THandler(*cuftheory);
    SimpSMTSolver* solver = new SimpSMTSolver(c, *thandler);
    MainSolver* mainSolver_ = new MainSolver(*thandler, c, solver, "test solver");
    MainSolver& mainSolver = *mainSolver_;
    BVLogic& logic = cuftheory->getLogic();

   // PTRef k = logic.mkBVNumVar("k"); no need for it; by using mkBVMod it is already in the server.
    PTRef a = logic.mkBVNumVar("a");
    PTRef b = logic.mkBVNumVar("b");
    PTRef e = logic.mkBVNumVar("e");
	PTRef f = logic.mkBVNumVar("f");
	PTRef g = logic.mkBVNumVar("g");
	PTRef h = logic.mkBVNumVar("h");
	PTRef d = logic.mkBVNumVar("d");
	PTRef d_p = logic.mkBVNumVar("d_p");

    PTRef eq_eg = logic.mkBVEq(e, g);
    PTRef eq_fh = logic.mkBVEq(f, h);

    PTRef const2 = logic.mkBVConst(2);
 //   PTRef eq_two = logic.mkBVEq(k, const2);

    PTRef c1 = logic.mkBVNumVar("c1");
    PTRef c2 = logic.mkBVNumVar("c2");

    PTRef mod1 = logic.mkBVMod(a, const2);
    PTRef mod2 = logic.mkBVMod(b, const2);
    PTRef plus1 = logic.mkBVPlus(mod1, mod2);
    PTRef mod3 = logic.mkBVMod(plus1, const2);
    PTRef eq1= logic.mkBVEq(mod3, c1);

    PTRef plus2 = logic.mkBVPlus(a, b);
    PTRef mod4 = logic.mkBVMod(plus2, const2);
    PTRef eq2 = logic.mkBVEq(mod4, c2);

    PTRef mul1 = logic.mkBVTimes(e, c1);
    PTRef mul2 = logic.mkBVTimes(mul1, f);
    PTRef eq3= logic.mkBVEq(mul2, d);

    PTRef mul3 = logic.mkBVTimes(g, c2);
    PTRef mul4 = logic.mkBVTimes(mul3, h);
    PTRef eq4= logic.mkBVEq(mul4, d_p);

    PTRef NotEq = logic.mkBVNeq(c1, c2);

    PTRef constOne = logic.getTerm_BVOne();

    PTRef assert = logic.mkBVEq(constOne , NotEq);


	vec<PtAsgn> asgns;
	vec<DedElem> deds;
	vec<PTRef> foo;

	SolverId id = {42};
	BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);

	BVRef output1;
	lbool stat;
	stat = bbb.insertEq(eq1, output1);

	BVRef output2;
	stat = bbb.insertEq(eq2, output2);

	BVRef output3;
	stat = bbb.insertEq(eq3, output3);  //d

	BVRef output4;
	stat = bbb.insertEq(eq4, output4);  //d_p

//	BVRef output5;
//	stat = bbb.insertEq(eq5, output5);

	BVRef output6;
	stat = bbb.insertEq(eq_eg, output6);

	BVRef output7;
	stat = bbb.insertEq(eq_fh, output7);

//	BVRef output8;
//	stat = bbb.insertEq(eq_two, output8);

	BVRef output9;
	stat = bbb.insertEq(assert, output9);

	std::cout << logic.printTerm(eq1) << "\n";
	std::cout << logic.printTerm(eq2) << "\n";
	std::cout << logic.printTerm(eq3) << "\n";
	std::cout << logic.printTerm(eq4) << "\n";
	std::cout << logic.printTerm(NotEq) << "\n";
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
