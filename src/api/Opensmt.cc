#include "Opensmt.h"

#include "Global.h"

Opensmt::Opensmt(opensmt_logic _logic, const char* name, int bw)
{
    config = new SMTConfig();
    const char* msg;
    config->setOption(SMTConfig::o_time_queries, SMTOption(1), msg);
    switch(_logic)
    {
    case qf_uf:
    case qf_bool:
        theory = new UFTheory(*config);
        break;
    case qf_lra:
        theory = new LRATheory(*config);
        break;
    case qf_lia:
        theory = new LIATheory(*config);
        break;
    case qf_cuf:
        theory = new CUFTheory(*config , bw);
        break;
    default:
        opensmt_error("Theory not supported");
    }
    thandler = new THandler(*theory);
    solver = new SimpSMTSolver(*config, *thandler);
    mainSolver = new MainSolver(*thandler, *config, solver, name);
    mainSolver->initialize();
}

Opensmt::~Opensmt()
{
    delete mainSolver;
    delete solver;
    delete thandler;
    delete theory;
    delete config;
}
