/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef PARALLEL_MAINSPLITTER_H
#define PARALLEL_MAINSPLITTER_H

#include "MainSolver.h"
#include "SplitData.h"
#include "ScatterSplitter.h"
#include "OsmtInternalException.h"
#include "LookaheadSplitter.h"
#include "Splitter.h"

#include <cmath>

class MainSplitter : public MainSolver {

private:
    inline bool isSplitTypeScatter() const &       { return dynamic_cast<Splitter&>(ts.solver).isSplitTypeScatter(); }

    inline bool isSplitTypeNone()    const &       { return dynamic_cast<Splitter&>(ts.solver).isSplitTypeNone(); }

    inline PTPLib::net::Channel & getChannel() const { return getSplitter().getChannel(); }

    inline ScatterSplitter & getScatterSplitter()  { return dynamic_cast<ScatterSplitter&>(getSMTSolver()); }

    inline Splitter & getSplitter()  const         { return dynamic_cast<Splitter&>(ts.solver); }

    void notifyResult(sstat const & result);

    vec<PTRef> addToConjunction(std::vector<vec<PtAsgn>> const &) const;

    sstat solve_(vec<FrameId> & enabledFrames) override;

    sstat check() override;

public:
    MainSplitter(std::unique_ptr<Theory> t,std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> th,
                 std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & config, std::string name)
            : MainSolver(std::move(t), std::move(tm), std::move(th), std::move(ss),logic,config, std::move(name))
    {}

    sstat solve();

    std::vector<std::string> getPartitionClauses();

    void writeSplits(std::string const &)  const;

    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig &, THandler &, PTPLib::net::Channel &);

    inline TermMapper& getTermMapper() const { return *term_mapper;}
};


#endif //PARALLEL_MAINSPLITTER_H
