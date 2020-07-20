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
The result is SAT, manifesting spurious counter-example
 ************************************************/
#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>

int main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory* cuftheory = new CUFTheory(c, 8);
    MainSolver* mainSolver_ = new MainSolver(std::unique_ptr<Theory>(cuftheory), c, "test solver");
    MainSolver& mainSolver = *mainSolver_;
    BVLogic& logic = cuftheory->getLogic();

    PTRef a = logic.mkCUFNumVar("a");
    PTRef b = logic.mkCUFNumVar("b");
    PTRef e = logic.mkCUFNumVar("e");
	PTRef f = logic.mkCUFNumVar("f");
	PTRef g = logic.mkCUFNumVar("g");
	PTRef h = logic.mkCUFNumVar("h");
	PTRef d = logic.mkCUFNumVar("d");
	PTRef d_p = logic.mkCUFNumVar("d_p");

	PTRef eq_eg = logic.mkEq(e, g);
	PTRef eq_fh = logic.mkEq(f, h);

    PTRef const2 = logic.mkCUFConst(2);

    PTRef c1 = logic.mkCUFNumVar("c1");
    PTRef c2 = logic.mkCUFNumVar("c2");

    PTRef mod1 = logic.mkCUFMod(a, const2);
    PTRef mod2 = logic.mkCUFMod(b, const2);
    PTRef plus1 = logic.mkCUFPlus(mod1, mod2);
    PTRef mod3 = logic.mkCUFMod(plus1, const2);
    PTRef eq1= logic.mkEq(mod3, c1);

    PTRef plus2 = logic.mkCUFPlus(a, b);
    PTRef mod4 = logic.mkCUFMod(plus2, const2);
    PTRef eq2 = logic.mkEq(mod4, c2);

    PTRef mul1 = logic.mkCUFTimes(e, c1);
    PTRef mul2 = logic.mkCUFTimes(mul1, f);
    PTRef eq3= logic.mkEq(mul2, d);


    PTRef mul3 = logic.mkCUFTimes(g, c2);
    PTRef mul4 = logic.mkCUFTimes(mul3, h);
    PTRef eq4= logic.mkEq(mul4, d_p);

    PTRef NotEq = logic.mkCUFNeq(d, d_p); //?

//    PTRef constOne = logic.getTerm_CUFOne();
//
//    PTRef assert = logic.mkEq(constOne , NotEq);


    SolverId id = { 5 };
	vec<PtAsgn> asgns;
	vec<PTRef> foo;

	char* msg;
	mainSolver.insertFormula(eq1, &msg);

	mainSolver.insertFormula(eq2, &msg);

	mainSolver.insertFormula(eq3, &msg);

	mainSolver.insertFormula(eq4, &msg);

	mainSolver.insertFormula(eq_eg, &msg);

	mainSolver.insertFormula(eq_fh, &msg);

	mainSolver.insertFormula(NotEq, &msg);

//	mainSolver.insertFormula(eq_two, & msg);

/*	BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);

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
	stat = bbb.insertEq(eq0, output6);

	BVRef output7;
	stat = bbb.insertEq(eq00, output7);

	BVRef output8;
	stat = bbb.insertEq(eq_two, output8);

	BVRef output9;
	stat = bbb.insertEq(assert, output9);*/

	std::cout << logic.printTerm(eq1) << "\n";
	std::cout << logic.printTerm(eq2) << "\n";
	std::cout << logic.printTerm(eq3) << "\n";
	std::cout << logic.printTerm(eq4) << "\n";
	std::cout << logic.printTerm(NotEq) << "\n";
	//std::cout << logic.printTerm(assert) << "\n";
    sstat r = mainSolver.check();

    ValPair v_a = mainSolver.getValue(a);
    std::cout << v_a.val << "\n";

    ValPair v_b = mainSolver.getValue(b);
    std::cout << v_b.val << "\n";

    ValPair v_c1 = mainSolver.getValue(c1);
    std::cout << v_c1.val << "\n";

	ValPair v_c2 = mainSolver.getValue(c2);
	std::cout << v_c2.val << "\n";

	ValPair v_d = mainSolver.getValue(d);
	std::cout << v_d.val << "\n";

	ValPair v_dp = mainSolver.getValue(d_p);
	std::cout << v_dp.val << "\n";

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


