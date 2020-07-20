#include <opensmt/opensmt2.h>
#include <opensmt/BitBlaster.h>
#include <stdio.h>

int
main(int argc, char** argv)
{

    if (argc != 3)
    {
        printf("Test Glue: set a & b to values in BV and compares their equality on EUF\n");
        printf("Usage: %s <a> <b>\n", argv[0]);
        return 1;
    }
    int c1_int = atoi(argv[1]);
    int c2_int = atoi(argv[2]);
    SMTConfig c;
    CUFTheory* cuftheory = new CUFTheory(c, 8);
    THandler* thandler = new THandler(*cuftheory);
    SimpSMTSolver* solver = new SimpSMTSolver(c, *thandler);
    MainSolver* mainSolver_ = new MainSolver(std::unique_ptr<Theory>(cuftheory), c, "test solver");
    MainSolver& mainSolver = *mainSolver_;
    BVLogic& logic = cuftheory->getLogic();

    PTRef a = logic.mkCUFNumVar("a");
    PTRef b = logic.mkCUFNumVar("b");
    PTRef a_bv = logic.mkBVNumVar("a");
    PTRef b_bv = logic.mkBVNumVar("b");
    PTRef c1 = logic.mkBVConst(c1_int);
    PTRef c2 = logic.mkBVConst(c2_int);

    PTRef eq1 = logic.mkBVEq(a_bv, c1);
    PTRef eq2 = logic.mkBVEq(b_bv, c2);
    PTRef eq3 = logic.mkEq(a, b);

    char* msg;
    mainSolver.insertFormula(eq3, &msg);

    vec<PtAsgn> asgns;
    vec<PTRef> foo;

    SolverId id = {42};
    BitBlaster bbb(id, c, mainSolver, logic, asgns, foo);
    BVRef output;

    lbool stat;
    bbb.insertEq(eq1, output);
    bbb.insertEq(eq2, output);

    bbb.bindCUFToBV(a, a_bv);
    bbb.bindCUFToBV(b, b_bv);

//    bbb.notifyEquality(eq3);

    sstat r = mainSolver.check();

    if (r == s_True) {
        printf("sat\n");
        bbb.computeModel();
        ValPair v = bbb.getValue(a_bv);
        printf("%s\n", v.val);
        ValPair u = mainSolver.getValue(a);
        printf("%s\n", u.val);

    }
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
