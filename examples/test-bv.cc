#include <opensmt/opensmt2.h>
#include <opensmt/BitBlaster.h>
#include <stdio.h>

int
main(int argc, char** argv)
{

    if (argc != 5)
    {
        printf("Computes a <op> b on bit width <bw>\n");
        printf("Usage: %s <bw> <op> <a> <b>\n", argv[0]);
        return 1;
    }
    char* op = argv[2];
    int c1_int = atoi(argv[3]);
    int c2_int = atoi(argv[4]);
    int bw = atoi(argv[1]);

    SMTConfig c;
    CUFTheory cuftheory(c, bw);
    THandler thandler(c, cuftheory);
    SimpSMTSolver solver(c, thandler);
    MainSolver mainSolver(thandler, c, &solver);

    BVLogic& logic = cuftheory.getLogic();

    PTRef a = logic.mkBVNumVar("a");
    PTRef b = logic.mkBVNumVar("b");
    PTRef c1 = logic.mkBVConst(c1_int);
    PTRef c2 = logic.mkBVConst(c2_int);

    PTRef eq1 = logic.mkBVEq(a, c1);
    PTRef eq2 = logic.mkBVEq(b, c2);

    PTRef op_tr;
    if (strcmp(op, "/") == 0)
        op_tr = logic.mkBVDiv(a, b);
    else if (strcmp(op, "*") == 0)
        op_tr = logic.mkBVTimes(a, b);
    else if (strcmp(op, "+") == 0)
        op_tr = logic.mkBVPlus(a, b);
    else if (strcmp(op, "-") == 0)
        op_tr = logic.mkBVMinus(a, b);
    else if (strcmp(op, "s<") == 0)
        op_tr = logic.mkBVSlt(a, b);
    else if (strcmp(op, "s<=") == 0)
        op_tr = logic.mkBVSleq(a, b);
    else if (strcmp(op, "u<=") == 0)
        op_tr = logic.mkBVUleq(a, b);
    else if (strcmp(op, "s>=") == 0)
        op_tr = logic.mkBVSgeq(a, b);
    else if (strcmp(op, "s>") == 0)
        op_tr = logic.mkBVSgt(a, b);
    else if (strcmp(op, "<<") == 0)
        op_tr = logic.mkBVLshift(a, b);
    else if (strcmp(op, ">>") == 0)
        op_tr = logic.mkBVRshift(a, b);
    else if (strcmp(op, "%") == 0)
        op_tr = logic.mkBVMod(a, b);
    else if (strcmp(op, "&") == 0)
        op_tr = logic.mkBVBwAnd(a, b);
    else if (strcmp(op, "|") == 0)
        op_tr = logic.mkBVBwOr(a, b);
    else if (strcmp(op, "=") == 0)
        op_tr = logic.mkBVEq(a, b);
    else if (strcmp(op, "&&") == 0)
        op_tr = logic.mkBVLand(a, b);
    else if (strcmp(op, "^") == 0)
        op_tr = logic.mkBVBwXor(a, b);
    else if (strcmp(op, "==") == 0)
        op_tr = logic.mkBVEq(a, b);
    else {
        printf("Unknown operator: %s", op);
        return 1;
    }

    PTRef d = logic.mkBVNumVar("d");

    PTRef eq3 = logic.mkBVEq(op_tr, d);

    SolverId id = { 5 };
    vec<PtAsgn> asgns;
    vec<DedElem> deds;
    vec<PTRef> foo;

    BitBlaster bbb(id, c, mainSolver, logic, asgns, deds, foo);
    BVRef output;

    lbool stat;
    stat = bbb.insertEq(eq1, output);
    bbb.insertEq(eq2, output);
    bbb.insertEq(eq3, output);

    sstat r = mainSolver.check();

    if (r == s_True) {
        printf("sat\n");
        bbb.computeModel();
        ValPair v = bbb.getValue(d);
        printf("%s\n", v.val);

    }
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
