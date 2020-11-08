//
// Created by Martin Blicha on 27.07.20.
//

#include "LogicFactory.h"

#include "LRALogic.h"
#include "LIALogic.h"
#include "BVLogic.h"
#include "OsmtApiException.h"

#include <array>

std::array<std::string, 19> logicToName = {{"Undef", "Empty", "QF_UF", "QF_CUF", "QF_BV", "QF_RDL", "QF_IDL",
                                           "QF_LRA", "QF_LIA", "QF_UFRDL", "QF_UFIDL", "QF_UFLRA", "QF_UFLIA",
                                           "QF_UFBV", "QF_AX", "QF_AXDIFF", "QF_BOOL", "QF_AUFBV", "QF_CT"}};

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


Logic * opensmt::LogicFactory::getInstance(Logic_t logicType) {
    Logic * l = nullptr;
    switch (logicType) {
        case Logic_t::QF_RDL:
        case Logic_t::QF_LRA:
        case Logic_t::QF_UFLRA:
        case Logic_t::QF_UFRDL:
        {
            l = new LRALogic();
            break;
        }
        case Logic_t::QF_IDL:
        case Logic_t::QF_UFIDL:
        case Logic_t::QF_LIA:
        case Logic_t::QF_UFLIA:
        {
            l = new LIALogic();
            break;
        }
        case Logic_t::QF_UF:
        case Logic_t::QF_BOOL:
        {
            l = new Logic();
            break;
        }
        case Logic_t::QF_CUF:
        {
            l = new BVLogic();
            break;
        }
        default:
            assert(false);
            throw OsmtApiException{"No logic or unsupported logic specified"};
    }
    return l;
}

LRALogic * opensmt::LogicFactory::getLRAInstance() { return new LRALogic(); }

LIALogic * opensmt::LogicFactory::getLIAInstance() { return new LIALogic(); }

