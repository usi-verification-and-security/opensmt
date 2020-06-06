#include "Opensmt.h"

#include "Global.h"

Opensmt::Opensmt(opensmt_logic _logic, const char* name, int bw)
{
    config = std::unique_ptr<SMTConfig>(new SMTConfig());
    const char* msg;
    config->setOption(SMTConfig::o_time_queries, SMTOption(1), msg);
    Theory * theory_raw_ptr = nullptr;
    switch(_logic)
    {
    case qf_uf:
    case qf_bool:
        theory_raw_ptr = new UFTheory(*config);
        break;
    case qf_lra:
        theory_raw_ptr = new LRATheory(*config);
        break;
    case qf_lia:
        theory_raw_ptr = new LIATheory(*config);
        break;
    case qf_cuf:
        theory_raw_ptr = new CUFTheory(*config , bw);
        break;
    default:
        opensmt_error("Theory not supported");
    }
    theory = std::unique_ptr<Theory>(theory_raw_ptr);
    thandler = std::unique_ptr<THandler>(new THandler(*theory));
    solver = std::unique_ptr<SimpSMTSolver>(new SimpSMTSolver(*config, *thandler));
    mainSolver = std::unique_ptr<MainSolver>(new MainSolver(*thandler, *config, solver.get(), name));
    mainSolver->initialize();
}

Opensmt::Opensmt(opensmt_logic _logic, const char* name, std::unique_ptr<SMTConfig> config)
{
    config->setTimeQueries();
    Theory * theory_raw_ptr = nullptr;
    switch(_logic)
    {
        case qf_uf:
        case qf_bool:
            theory_raw_ptr = new UFTheory(*config);
            break;
        case qf_lra:
            theory_raw_ptr = new LRATheory(*config);
            break;
        case qf_lia:
            theory_raw_ptr = new LIATheory(*config);
            break;
        case qf_cuf:
            theory_raw_ptr = new CUFTheory(*config , config->cuf_bitwidth);
            break;
        default:
        opensmt_error("Theory not supported");
    }
    this->config = std::move(config);
    theory = std::unique_ptr<Theory>(theory_raw_ptr);
    thandler = std::unique_ptr<THandler>(new THandler(*theory));
    solver = std::unique_ptr<SimpSMTSolver>(new SimpSMTSolver(*this->config, *thandler));
    mainSolver = std::unique_ptr<MainSolver>(new MainSolver(*thandler, *this->config, solver.get(), name));
    mainSolver->initialize();
}

Opensmt::~Opensmt()
{

}
