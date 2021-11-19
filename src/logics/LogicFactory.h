//
// Created by Martin Blicha on 27.07.20.
//

#ifndef OPENSMT_LOGICFACTORY_H
#define OPENSMT_LOGICFACTORY_H

#include <string>

class Logic;
class ArithLogic;

namespace opensmt {

enum class Logic_t : int {
    UNDEF, EMPTY, QF_UF, QF_CUF, QF_BV, QF_RDL, QF_IDL, QF_LRA, QF_LIA, QF_NIA, QF_NRA, QF_LIRA, QF_NIRA, QF_UFRDL, QF_UFIDL,
    QF_UFLRA, QF_UFLIA, QF_UFBV, QF_AX, QF_AXDIFF, QF_BOOL, QF_AUFBV, QF_CT
};

Logic_t getLogicFromString(const std::string & name);

std::string getStringFromLogic(const Logic_t logic);


class LogicFactory {
public:
    static Logic * getInstance(Logic_t);
    static ArithLogic * getLRAInstance();
    static ArithLogic * getLIAInstance();
};
}
#endif //OPENSMT_LOGICFACTORY_H
