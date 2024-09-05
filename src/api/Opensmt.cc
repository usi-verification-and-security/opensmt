#include "Opensmt.h"
#include "MainSolver.h"

#include <logics/LogicFactory.h>

namespace opensmt {

namespace {
    Logic_t convert(opensmt_logic logic) {
        switch (logic) {
            case qf_lra:
                return Logic_t::QF_LRA;
            case qf_lia:
                return Logic_t::QF_LIA;
            case qf_bool:
                return Logic_t::QF_BOOL;
            case qf_bv:
                return Logic_t::QF_BV;
            case qf_uf:
                return Logic_t::QF_UF;
            case qf_idl:
                return Logic_t::QF_IDL;
            case qf_rdl:
                return Logic_t::QF_RDL;
            case qf_ufidl:
                return Logic_t::QF_UFIDL;
            case qf_uflra:
                return Logic_t::QF_UFLRA;
            case qf_ufrdl:
                return Logic_t::QF_UFRDL;
            case qf_uflia:
                return Logic_t::QF_UFLIA;
            case qf_ax:
                return Logic_t::QF_AX;
            case qf_alra:
                return Logic_t::QF_ALRA;
            case qf_alia:
                return Logic_t::QF_ALIA;
            case qf_auflra:
                return Logic_t::QF_AUFLRA;
            case qf_auflia:
                return Logic_t::QF_AUFLIA;
            case qf_auflira:
                return Logic_t::QF_AUFLIRA;
            default:
                return Logic_t::UNDEF;
        }
    }
} // namespace

Opensmt::Opensmt(opensmt_logic _logic, char const * name) {
    config = std::unique_ptr<SMTConfig>(new SMTConfig());
    logic.reset(LogicFactory::getInstance(convert(_logic)));
    mainSolver = std::unique_ptr<MainSolver>(new MainSolver(*logic, *config, name));
}

Opensmt::Opensmt(opensmt_logic logic_, char const * name, std::unique_ptr<SMTConfig> config_) {
    this->config = std::move(config_);
    logic.reset(LogicFactory::getInstance(convert(logic_)));
    mainSolver = std::unique_ptr<MainSolver>(new MainSolver(*logic, *this->config, name));
}

} // namespace opensmt
