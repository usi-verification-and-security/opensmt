//
// Created by Martin Blicha on 27.07.20.
//

#include "LogicFactory.h"

#include "LRALogic.h"
#include "LIALogic.h"
#include "BVLogic.h"


Logic * opensmt::LogicFactory::getInstance(SMTConfig & config) {
    auto logicType = config.getLogic();
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
            throw std::logic_error{"No logic or unsupported logic specified"};
    }
    return l;
}

LRALogic * opensmt::LogicFactory::getLRAInstance() { return new LRALogic(); }

LIALogic * opensmt::LogicFactory::getLIAInstance() { return new LIALogic(); }

