//
// Created by Martin Blicha on 06.05.21.
//

#ifndef OPENSMT_RDLOGIC_H
#define OPENSMT_RDLOGIC_H

#include "LRALogic.h"

class RDLogic : public LRALogic {
    const opensmt::Logic_t getLogic() const override {
        return opensmt::Logic_t::QF_RDL;
    }

    const char* getName() const override {
        return "QF_RDL";
    }
};

#endif //OPENSMT_RDLOGIC_H
