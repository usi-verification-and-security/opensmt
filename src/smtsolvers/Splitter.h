/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_SPLITTER_H
#define OPENSMT_SPLITTER_H

#include "SplitData.h"
#include "SplitContext.h"

class Splitter {

protected:
    SplitContext splitContext;

public:
    Splitter(SMTConfig & c, uint64_t & d)
    : splitContext(c, d)
    {}

    std::vector<SplitData>      const & getSplits() { return splitContext.getSplits(); }

    bool isSplitTypeScatter()   const  { return splitContext.isSplitTypeScatter(); }

    bool isSplitTypeLookahead()  const { return splitContext.isSplitTypeLookahead(); }

    bool isSplitTypeNone()       const { return splitContext.isSplitTypeNone(); }

    void resetSplitType() { splitContext.resetSplitType(); }
};

#endif //OPENSMT_SPLITTER_H
