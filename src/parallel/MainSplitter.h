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
    inline bool isSplitTypeScatter() const       { return dynamic_cast<Splitter const &>(getSMTSolver()).isSplitTypeScatter(); }

    inline bool isSplitTypeNone()    const       { return dynamic_cast<Splitter const &>(getSMTSolver()).isSplitTypeNone(); }

    inline PTPLib::net::Channel<PTPLib::net::SMTS_Event, PTPLib::net::Lemma> & getChannel() const { return getSplitter().getChannel(); }

    inline ScatterSplitter const & getScatterSplitter() const { return dynamic_cast<ScatterSplitter const &>(getSMTSolver()); }
    inline ScatterSplitter & getScatterSplitter()             { return dynamic_cast<ScatterSplitter &>(getSMTSolver()); }

    inline Splitter const & getSplitter()  const   { return dynamic_cast<Splitter const &>(getSMTSolver()); }
    inline Splitter & getSplitter()                { return dynamic_cast<Splitter &>(getSMTSolver()); }

    void notifyResult(sstat const & result);

    vec<PTRef> addToConjunction(std::vector<vec<PtAsgn>> const &) const;

    sstat solve_(vec<FrameId> const & enabledFrames) override;

    sstat check() override;

    void throwWithLocationInfo(std::string const & str) const {
        std::scoped_lock<std::mutex> s_lk(getChannel().getMutex());
        throw OsmtInternalException(getChannel().get_current_header().at(PTPLib::common::Param.NODE + " " + str));
    }

    bool verifyPartitions(vec<PTRef> const & partitions) const;

public:
    MainSplitter(std::unique_ptr<Theory> t,std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> th,
                 std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & config, std::string name)
            : MainSolver(std::move(t), std::move(tm), std::move(th), std::move(ss),logic,config, std::move(name))
    {}

    sstat solve();

    std::vector<std::string> getPartitionClauses() const;

    void writeSplits(std::string const &)  const;

    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig &, THandler &, PTPLib::net::Channel<PTPLib::net::SMTS_Event, PTPLib::net::Lemma> &);
};


#endif //PARALLEL_MAINSPLITTER_H
