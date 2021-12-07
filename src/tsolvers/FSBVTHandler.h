/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_FSBVTHANDLER_H
#define OPENSMT_FSBVTHANDLER_H

#include "TSolverHandler.h"
#include "FSBVLogic.h"
#include "OsmtInternalException.h"

class FSBVTHandler : public TSolverHandler
{
private:
    FSBVLogic & logic;
public:
    FSBVTHandler(SMTConfig & c, FSBVLogic & l);
    ~FSBVTHandler() override = default;
    Logic & getLogic() override { return logic; }
    Logic const & getLogic() const override { return logic; }

    PTRef getInterpolant(const ipartitions_t & mask, map<PTRef, icolor_t> * labels, PartitionManager & pmanager) override { throw OsmtInternalException("Operation not supported for FSBVLoogic"); };

    lbool getPolaritySuggestion(PTRef pt) const override { return l_True; };
};
#endif //OPENSMT_FSBVTHANDLER_H
