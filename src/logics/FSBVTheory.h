/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_FSBVTHEORY_H
#define OPENSMT_FSBVTHEORY_H

#include "Theory.h"
#include "FSBVLogic.h"
#include "FSBVTHandler.h"

class FSBVTheory : public Theory
{
private:
    FSBVLogic & logic;
    FSBVTHandler fsbvtshandler;
    std::unordered_map<PTRef,PTRef,PTRefHash> bbTermToBVTerm;
public:
    FSBVTheory(SMTConfig & c, FSBVLogic & logic)
        : Theory(c)
        , logic(logic)
        , fsbvtshandler(c, logic)
    { }
    virtual FSBVLogic & getLogic() override { return logic; }
    virtual const FSBVLogic & getLogic() const override { return logic; }
    virtual FSBVTHandler & getTSolverHandler() override { return fsbvtshandler; }
    virtual bool simplify(const vec<PFRef>&, PartitionManager&, int) override;
    const std::unordered_map<PTRef, PTRef, PTRefHash> & getBBTermToBVTerm() const { return bbTermToBVTerm; }
};

#endif //OPENSMT_FSBVTHEORY_H
