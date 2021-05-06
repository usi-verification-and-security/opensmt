//
// Created by Martin Blicha on 06.05.21.
//

#ifndef OPENSMT_IDLOGIC_H
#define OPENSMT_IDLOGIC_H

#include "LIALogic.h"

class IDLogic : public LIALogic {
    const opensmt::Logic_t getLogic() const override {
        return opensmt::Logic_t::QF_IDL;
    }

    const char* getName() const override {
        return "QF_IDL";
    }
};

#endif //OPENSMT_IDLOGIC_H
