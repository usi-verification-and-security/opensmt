#include <opensmt/opensmt2.h>
#include <stdio.h>

int
main(int argc, char** argv)
{
    Logic logic; // UF Logic
    SMTConfig c;
    MainSolver* mainSolver_ = new MainSolver(logic, c, "test solver");
    MainSolver& mainSolver = *mainSolver_;

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
        auto m = mainSolver.getModel();
        char * v1_p = logic.pp(m->evaluate(v1));
        char * v2_p = logic.pp(m->evaluate(v2));
        char* var_a_s = logic.pp(v1);
        char* var_b_s = logic.pp(v2);

        printf("var %s has value %s\n", var_a_s, v1_p);
        printf("var %s has value %s\n", var_b_s, v2_p);
        free(var_a_s);
        free(var_b_s);
        free(v1_p);
        free(v2_p);
    }
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
