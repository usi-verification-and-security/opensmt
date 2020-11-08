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
    //int c1_int = atoi(argv[3]);
    //int c2_int = atoi(argv[4]);
    const char* c1_str = argv[3];
    const char* c2_str = argv[4];
    int bw = atoi(argv[1]);

    SMTConfig c;
    BVLogic* logic_ = new BVLogic(bw);
    BVLogic& logic = *logic_;
    MainSolver* mainSolver_ = new MainSolver(logic, c, "test solver");
    MainSolver& mainSolver = *mainSolver_;

    PTRef a = logic.mkBVNumVar("a");
    PTRef b = logic.mkBVNumVar("b");
    //PTRef c1 = logic.mkBVConst(c1_int);
    PTRef c1 = logic.mkBVConst(c1_str);
    //PTRef c2 = logic.mkBVConst(c2_int);
    PTRef c2 = logic.mkBVConst(c2_str);

    PTRef eq1 = logic.mkBVEq(a, c1);
    PTRef eq2 = logic.mkBVEq(b, c2);

    //printf("Computing %d (%s) %s %d (%s)\n", c1_int, logic.printTerm(c1), op, c2_int, logic.printTerm(c2));
    printf("Computing %s (%s) %s %s (%s)\n", c1_str, logic.printTerm(c1), op, c2_str, logic.printTerm(c2));


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
    else if (strcmp(op, "a>>") == 0)
        op_tr = logic.mkBVARshift(a, b);
    else if (strcmp(op, "l>>") == 0)
        op_tr = logic.mkBVLRshift(a, b);
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

    vec<PtAsgn> asgns;
    vec<PTRef> foo;

    SolverId id = {42};
    BitBlaster bbb(id, c, mainSolver, logic, asgns, foo);
    BVRef output;

    lbool stat;
    stat = bbb.insertEq(eq1, output);
    bbb.insertEq(eq2, output);
    bbb.insertEq(eq3, output);

    char* msg;
    mainSolver.insertFormula(logic.getTerm_true(), &msg);

    sstat r = mainSolver.check();

    if (r == s_True) {
        printf("sat\n");
        bbb.computeModel();
        ValPair v = bbb.getValue(d);
        char* bin;
        opensmt::wordToBinary(atoi(v.val), bin, bw);
        printf("%s (%s)\n", v.val, bin);

    }
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
