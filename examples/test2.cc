#include <opensmt/opensmt2.h>
#include <stdio.h>

int
main(int argc, char** argv)
{
    SMTConfig c;
    UFTheory* uftheory = new UFTheory(c);
    THandler* thandler = new THandler(c, *uftheory);
    SimpSMTSolver* solver = new SimpSMTSolver(c, *thandler);
    MainSolver* mainSolver_ = new MainSolver(*thandler, c, solver, "test solver");
    MainSolver& mainSolver = *mainSolver_;

    Logic& logic = thandler->getLogic();

    PTRef v1 = logic.mkBoolVar("a");
    PTRef v2 = logic.mkBoolVar("b");
    vec<PTRef> args;

    args.push(logic.mkNot(v1));
    args.push(logic.mkNot(v2));
    mainSolver.push(logic.mkOr(args));

    args.clear();
    args.push(v1);
    args.push(logic.mkNot(v2));
    mainSolver.push(logic.mkOr(args));

    args.clear();
    args.push(logic.mkNot(v1));
    args.push(v2);
    mainSolver.push(logic.mkOr(args));

    sstat r = mainSolver.check();

    if (r == s_True) {
        printf("sat\n");
        ValPair v1_p = mainSolver.getValue(v1);
        ValPair v2_p = mainSolver.getValue(v2);
        char* var_a_s = logic.printTerm(v1_p.tr);
        char* var_b_s = logic.printTerm(v2_p.tr);

        printf("var %s has value %s\n", var_a_s, v1_p.val);
        printf("var %s has value %s\n", var_b_s, v2_p.val);
        free(var_a_s);
        free(var_b_s);
    }
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
