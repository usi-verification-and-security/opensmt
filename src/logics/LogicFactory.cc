//
// Created by Martin Blicha on 27.07.20.
//

#include "LogicFactory.h"

#include "ArithLogic.h"
#include "BVLogic.h"
#include "OsmtApiException.h"

#include <array>

std::array<std::string, 23> logicToName = {{"Undef", "Empty", "QF_UF", "QF_CUF", "QF_BV", "QF_RDL", "QF_IDL",
                                           "QF_LRA", "QF_LIA", "QF_UFRDL", "QF_UFIDL", "QF_UFLRA", "QF_UFLIA",
                                           "QF_UFBV", "QF_AX", "QF_AXDIFF", "QF_ALRA", "QF_ALIA", "QF_AUFLRA",
                                           "QF_AUFLIA", "QF_BOOL", "QF_AUFBV", "QF_CT"}};

opensmt::Logic_t opensmt::getLogicFromString(const std::string& name) {
    if (name == "QF_UF") return opensmt::Logic_t::QF_UF;
    if (name == "QF_LRA") return opensmt::Logic_t::QF_LRA;
    if (name == "QF_RDL") return opensmt::Logic_t::QF_RDL;
    if (name == "QF_LIA") return opensmt::Logic_t::QF_LIA;
    if (name == "QF_IDL") return opensmt::Logic_t::QF_IDL;
    if (name == "QF_CUF") return opensmt::Logic_t::QF_CUF;
    if (name == "QF_UFLRA") return opensmt::Logic_t::QF_UFLRA;
    if (name == "QF_UFLIA") return opensmt::Logic_t::QF_UFLIA;
    if (name == "QF_UFRDL") return opensmt::Logic_t::QF_UFRDL;
    if (name == "QF_UFIDL") return opensmt::Logic_t::QF_UFIDL;
    if (name == "QF_AX") return opensmt::Logic_t::QF_AX;
    if (name == "QF_ALRA") return opensmt::Logic_t::QF_ALRA;
    if (name == "QF_ALIA") return opensmt::Logic_t::QF_ALIA;
    if (name == "QF_AUFLRA") return opensmt::Logic_t::QF_AUFLRA;
    if (name == "QF_AUFLIA") return opensmt::Logic_t::QF_AUFLIA;
    return opensmt::Logic_t::UNDEF;
}

std::string opensmt::getStringFromLogic(const opensmt::Logic_t logic) {
    return logicToName[static_cast<int>(logic)];
}


Logic * opensmt::LogicFactory::getInstance(Logic_t logicType) {
    Logic * l = nullptr;
    switch (logicType) {
        case Logic_t::QF_RDL:
        case Logic_t::QF_UFRDL:
        case Logic_t::QF_LRA:
        case Logic_t::QF_UFLRA:
        case Logic_t::QF_ALRA:
        case Logic_t::QF_AUFLRA:
        case Logic_t::QF_IDL:
        case Logic_t::QF_UFIDL:
        case Logic_t::QF_LIA:
        case Logic_t::QF_UFLIA:
        case Logic_t::QF_ALIA:
        case Logic_t::QF_AUFLIA:
        {
            l = new ArithLogic(logicType);
            break;
        }
        case Logic_t::QF_UF:
        case Logic_t::QF_BOOL:
        case Logic_t::QF_AX:
        {
            l = new Logic(logicType);
            break;
        }
        case Logic_t::QF_CUF:
        {
            l = new BVLogic(logicType);
            break;
        }
        default:
            assert(false);
            throw OsmtApiException{"No logic or unsupported logic specified"};
    }
    return l;
}

ArithLogic * opensmt::LogicFactory::getLRAInstance() { return new ArithLogic(Logic_t::QF_LRA); }

ArithLogic * opensmt::LogicFactory::getLIAInstance() { return new ArithLogic(Logic_t::QF_LIA); }

