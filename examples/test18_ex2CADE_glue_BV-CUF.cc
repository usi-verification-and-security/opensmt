/************************************************
* test18_ex2CADE_ glue_BV-CUF.cc
* Created on: Feb2, 2017
unsigned a;
unsigned b;
unsigned c1 = (((a % 2) + (b % 2))) % 2;     //eq1 between mod3 and c1
unsigned c2 = (a + b) % 2;                   //eq2
unsigned e, f;
e=g;
f=h;
unsigned d = e*f*c1;                        //eq3
unsigned d_p = g*h*c2;                      //eq4
assert(d == d_p);                           //assert ((d != d_p ) = 1)
}
 ************************************************/
#include <opensmt/opensmt2.h>
#include <stdio.h>
#include <opensmt/BitBlaster.h>

void printValue(ValPair vp, Logic& l)
{
    std::cout << l.printTerm(vp.tr) << " "  << vp.val << "\n";
}

int main(int argc, char** argv)
{
    SMTConfig c;
    CUFTheory* cuftheory = new CUFTheory(c, 8);
    THandler* thandler = new THandler(*cuftheory);
    SimpSMTSolver* solver = new SimpSMTSolver(c, *thandler);
    MainSolver* mainSolver_ = new MainSolver(*thandler, c, solver, "test solver");
    MainSolver& mainSolver = *mainSolver_;
    BVLogic& logic = cuftheory->getLogic();

    PTRef a = logic.mkCUFNumVar("a");
    PTRef b = logic.mkCUFNumVar("b");

    PTRef a_bv = logic.mkBVNumVar("a");
    PTRef b_bv = logic.mkBVNumVar("b");

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

//CUF version of C1
    PTRef mod1 = logic.mkCUFMod(a, const2);
    PTRef mod2 = logic.mkCUFMod(b, const2);
    PTRef plus1 = logic.mkCUFPlus(mod1, mod2);
    PTRef mod3 = logic.mkCUFMod(plus1, const2);
    PTRef eq1= logic.mkEq(mod3, c1);

// CUF version of C2
    PTRef plus2 = logic.mkCUFPlus(a, b);
    PTRef mod4 = logic.mkCUFMod(plus2, const2);
    PTRef eq2 = logic.mkEq(mod4, c2);

    PTRef mul1 = logic.mkCUFTimes(e, c1);
    PTRef mul2 = logic.mkCUFTimes(mul1, f);
    PTRef eq3= logic.mkEq(mul2, d);

    PTRef mul3 = logic.mkCUFTimes(g, c2);
    PTRef mul4 = logic.mkCUFTimes(mul3, h);
    PTRef eq4= logic.mkEq(mul4, d_p);

    PTRef NotEq = logic.mkCUFNeq(d, d_p);

//    PTRef constOne = logic.getTerm_CUFOne();
//
//    PTRef assert = logic.mkEq(constOne , NotEq);

    char* msg;
    mainSolver.insertFormula(eq1, &msg);

    mainSolver.insertFormula(eq2, &msg);

    mainSolver.insertFormula(eq3, &msg);

    mainSolver.insertFormula(eq4, &msg);

    mainSolver.insertFormula(eq_eg, &msg);

    mainSolver.insertFormula(eq_fh, &msg);

    mainSolver.insertFormula(NotEq, &msg);

//***********BV version of C1 and C2 and 2**************

    PTRef const2_bv = logic.mkBVConst(2);
    PTRef c1_bv = logic.mkBVNumVar("c1");
    PTRef c2_bv = logic.mkBVNumVar("c2");

// BV of C1
    PTRef mod1_bv = logic.mkBVMod(a_bv, const2_bv);
    PTRef mod2_bv = logic.mkBVMod(b_bv, const2_bv);
    PTRef plus1_bv = logic.mkBVPlus(mod1_bv, mod2_bv);
    PTRef mod3_bv = logic.mkBVMod(plus1_bv, const2_bv);
    PTRef eq1_bv= logic.mkBVEq(mod3_bv, c1_bv);
// BV of C2
    PTRef plus2_bv = logic.mkBVPlus(a_bv, b_bv);
    PTRef mod4_bv = logic.mkBVMod(plus2_bv, const2_bv);
    PTRef eq2_bv = logic.mkBVEq(mod4_bv, c2_bv);

//***** BItBlasting of C1_bv and C2_bv and two******
    vec<PtAsgn> asgns;
    vec<DedElem> deds;
    vec<PTRef> foo;
    SolverId id = {42};
    BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);

    BVRef output1;
    lbool stat;
    stat = bbb.insertEq(eq1_bv, output1);

    BVRef output2;
    stat = bbb.insertEq(eq2_bv, output2);
//********End of BitBlasting***********

//********bind CUF to BV left-hand-side & right-hand-side***********

    bbb.bindCUFToBV(mod3, mod3_bv);
    bbb.bindCUFToBV(mod4, mod4_bv);

//*******notify********
//  bbb.notifyEquality(eq1);
//  bbb.notifyEquality(eq2);
    bbb.notifyEqualities();

//  BVRef output4;
//  stat = bbb.insertEq(eq4, output4);  //d_p

//  BVRef output5;
//  stat = bbb.insertEq(eq5, output5);

//  BVRef output6;
//  stat = bbb.insertEq(eq_two, output6);

/*  BVRef output7;
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
    sstat r = mainSolver.check();


    if (r == s_True) {
        printf("sat\n");
        printValue(mainSolver.getValue(a), logic);
        printValue(mainSolver.getValue(b), logic);
        printValue(mainSolver.getValue(c1), logic);
        printValue(mainSolver.getValue(c2), logic);
        printValue(mainSolver.getValue(d), logic);
        printValue(mainSolver.getValue(d_p), logic);
    }
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
