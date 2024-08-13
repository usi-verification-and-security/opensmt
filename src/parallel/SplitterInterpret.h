/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef PARALLEL_SPLITTERINTERPRET_H
#define PARALLEL_SPLITTERINTERPRET_H

#include "MainSplitter.h"

#include <api/Interpret.h>

namespace opensmt::parallel {

class SplitterInterpret : public Interpret {
private:
    PTPLib::net::Channel<PTPLib::net::SMTS_Event, PTPLib::net::Lemma> & channel;
    bool search = true;

  protected:
    void                          writeSplits(const char* filename);
    std::unique_ptr<MainSolver>   createMainSolver(const char* logic_name) override;
    sstat                         checkSat()                               override;
    void                          exit()                                   override  { return; }

  public:

    SplitterInterpret(SMTConfig & c, PTPLib::net::Channel<PTPLib::net::SMTS_Event, PTPLib::net::Lemma> & ch)
    : Interpret(c)
    , channel(ch)
    { }

    virtual ~SplitterInterpret() = default;

    sstat interpSMTContent(char *content, vec<pair<int,int>> &&, bool, bool);

    inline MainSplitter & getMainSplitter() { return dynamic_cast<MainSplitter&>(getMainSolver()); };

    inline Splitter & getSplitter() {
        return dynamic_cast<Splitter&>(getMainSplitter().getSMTSolver());
    }
};

}

#endif //PARALLEL_SPLITTERINTERPRET_H
