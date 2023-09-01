#include <opensmt/opensmt2.h>
#include <stdio.h>

int main()
{
    Logic logic{opensmt::Logic_t::QF_UF}; // UF Logic
    SMTConfig c;
    MainSolver mainSolver(logic, c, "test solver");

    PTRef v1 = logic.mkBoolVar("a");
    PTRef v2 = logic.mkBoolVar("b");
    vec<PTRef> args;

    args.push(logic.mkNot(v1));
    args.push(logic.mkNot(v2));
    mainSolver.insertFormula(logic.mkOr(args));

    args.clear();
    args.push(v1);
    args.push(logic.mkNot(v2));
    mainSolver.insertFormula(logic.mkOr(args));

    args.clear();
    args.push(logic.mkNot(v1));
    args.push(v2);
    mainSolver.insertFormula(logic.mkOr(args));

    sstat r = mainSolver.check();

    if (r == s_True) {
        printf("sat\n");
        auto m = mainSolver.getModel();
        auto v1_p = logic.pp(m->evaluate(v1));
        auto v2_p = logic.pp(m->evaluate(v2));
        auto var_a_s = logic.pp(v1);
        auto var_b_s = logic.pp(v2);

        printf("var %s has value %s\n", var_a_s.c_str(), v1_p.c_str());
        printf("var %s has value %s\n", var_b_s.c_str(), v2_p.c_str());
    }
    else if (r == s_False)
        printf("unsat\n");
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
