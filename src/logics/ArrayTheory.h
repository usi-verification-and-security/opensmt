/*
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_ARRAYTHEORY_H
#define OPENSMT_ARRAYTHEORY_H

#include "Theory.h"
#include "ArrayTHandler.h"

class ArrayTheory : public Theory {
private:
    Logic &    logic;
    ArrayTHandler tshandler;
public:
    ArrayTheory(SMTConfig & c, Logic & logic)
    : Theory(c)
    , logic(logic)
    , tshandler(c, logic)
    { }

    ~ArrayTheory() {}
    virtual Logic&            getLogic() override { return logic; }
    virtual const Logic&      getLogic() const override { return logic; }
    virtual ArrayTHandler&       getTSolverHandler() override  { return tshandler; }
    virtual const ArrayTHandler& getTSolverHandler() const { return tshandler; }
    virtual bool simplify(vec<PFRef> const &, PartitionManager &, int) override;
};


#endif //OPENSMT_ARRAYTHEORY_H
