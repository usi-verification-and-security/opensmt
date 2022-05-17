/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef PARALLEL_SPLITTERINTERPRET_H
#define PARALLEL_SPLITTERINTERPRET_H

#include "MainSplitter.h"
#include "Interpret.h"

class SplitterInterpret : public Interpret {
private:
    PTPLib::net::Channel & channel;

  protected:
    void                          writeSplits(const char* filename);
    std::unique_ptr<MainSolver>   createMainSolver(const char* logic_name) override;
    sstat                          checkSat()                              override;

  public:

    SplitterInterpret(SMTConfig & c, PTPLib::net::Channel & ch)
    : Interpret(c)
    , channel(ch)
    { }

    virtual ~SplitterInterpret() = default;

    MainSolver&     getMainSplitter() { return *main_solver; }
};

#endif //PARALLEL_SPLITTERINTERPRET_H
