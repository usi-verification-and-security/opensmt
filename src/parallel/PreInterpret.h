/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef API_PREINTERPRET_H
#define API_PREINTERPRET_H

#include "MainSplitter.h"
#include "Interpret.h"

class PreInterpret : public Interpret {
private:
    PTPLib::net::Channel & channel;

  protected:
    void                          writeSplits(const char* filename);
    std::unique_ptr<MainSolver>   createMainSolver(const char* logic_name) override;
    bool                          checkSat()                               override;

  public:

    PreInterpret(SMTConfig & c, PTPLib::net::Channel & ch)
    : Interpret(c)
    , channel(ch)
    { }

    virtual ~PreInterpret() = default;

    MainSolver&     getMainSplitter() { return *main_solver; }
};

#endif
