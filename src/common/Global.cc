//
// Created by prova on 20.07.20.
//
#include "Global.h"

std::string logicToName[19] = {"Undef", "Empty", "QF_UF", "QF_CUF", "QF_BV", "QF_RDL", "QF_IDL",
               "QF_LRA", "QF_LIA", "QF_UFRDL", "QF_UFIDL", "QF_UFLRA", "QF_UFLIA",
               "QF_UFBV", "QF_AX", "QF_AXDIFF", "QF_BOOL", "QF_AUFBV", "QF_CT"};

opensmt::Logic_t opensmt::getLogicFromString(const std::string& name) {
    if (name == "QF_UF") return opensmt::Logic_t::QF_UF;
    if (name == "QF_LRA") return opensmt::Logic_t::QF_LRA;
    if (name == "QF_RDL") return opensmt::Logic_t::QF_RDL;
    if (name == "QF_LIA") return opensmt::Logic_t::QF_LIA;
    if (name == "QF_IDL") return opensmt::Logic_t::QF_IDL;
    if (name == "QF_CUF") return opensmt::Logic_t::QF_CUF;
    if (name == "QF_UFLRA") return opensmt::Logic_t::QF_UFLRA;
    return opensmt::Logic_t::UNDEF;
}

std::string opensmt::getStringFromLogic(const opensmt::Logic_t logic) {
    return logicToName[static_cast<int>(logic)];
}