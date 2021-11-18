#include <opensmt/opensmt2.h>
#include <stdio.h>

Opensmt*
pre()
{
    Opensmt* osmt = new Opensmt(opensmt_logic::qf_lra, "test solver");
    return osmt;
}

int
main(int argc, char** argv)
{

    Opensmt* osmt = pre();
    SMTConfig& c = osmt->getConfig();
    MainSolver& mainSolver = osmt->getMainSolver();
    SimpSMTSolver& solver = osmt->getSolver();
    auto & logic = osmt->getLRALogic();

    const char* msg;
//    c.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);

    // Create the constant
    PTRef cons = logic.mkRealConst(-1);

    // assertion (<= -1 0)
    PTRef le1 = logic.mkLeq(cons, logic.getTerm_RealZero());

    mainSolver.push(le1);

    // Check
    sstat r = mainSolver.check();

    if (r == s_True)
        printf("sat\n");
    else if (r == s_False)
    {
        printf("unsat\n");
    }
    else if (r == s_Undef)
        printf("unknown\n");
    else
        printf("error\n");

    return 0;
}
