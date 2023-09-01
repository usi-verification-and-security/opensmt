#include <opensmt/opensmt2.h>
#include <stdio.h>

int main()
{
    Logic logic{opensmt::Logic_t::QF_UF}; // UF Logic
    SMTConfig c;
    MainSolver mainSolver(logic, c, "test solver");
    PTRef v = logic.mkBoolVar("a");
    PTRef v_neg = logic.mkNot(v);
    vec<PTRef> args;
    args.push(v);
    args.push(v_neg);
    PTRef a = logic.mkAnd(args);

    mainSolver.insertFormula(a);
    printf("Running check!\n");
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
