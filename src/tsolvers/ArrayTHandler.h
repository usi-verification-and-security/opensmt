/*
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_ARRAYTHANDLER_H
#define OPENSMT_ARRAYTHANDLER_H

#include "TSolverHandler.h"
#include "arraysolver/ArraySolver.h"

namespace opensmt {

class ArrayTHandler : public TSolverHandler {
    Logic & logic;
    Egraph * egraph;
    ArraySolver * arraySolver;
public:
    ArrayTHandler(SMTConfig & c, Logic & l);

    Logic & getLogic() override { return logic; };

    Logic const & getLogic() const override { return logic; }

    PTRef getInterpolantImpl(const ipartitions_t & , ItpColorMap *, PartitionManager &) override { throw InternalException("Interpolation not supported yet"); };

};

}

#endif //OPENSMT_ARRAYTHANDLER_H
