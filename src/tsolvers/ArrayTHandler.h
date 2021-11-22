/*
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_ARRAYTHANDLER_H
#define OPENSMT_ARRAYTHANDLER_H

#include "ArraySolver.h"
#include "TSolverHandler.h"

class ArrayTHandler : public TSolverHandler {
    Logic & logic;
    Egraph * egraph;
    ArraySolver * arraySolver;
public:
    ArrayTHandler(SMTConfig & c, Logic & l);

    ~ArrayTHandler() override;

    void clearSolver() override;

    Logic & getLogic() override;

    const Logic & getLogic() const override;

    PTRef getInterpolant(const ipartitions_t & mask, map<PTRef, icolor_t> *map1, PartitionManager & pmanager) override;

    lbool getPolaritySuggestion(PTRef pt) const override;
};


#endif //OPENSMT_ARRAYTHANDLER_H
