/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_MAINCOUNTER_H
#define OPENSMT_MAINCOUNTER_H

#include "MainSolver.h"
#include "ClausePrinter.h"

class MainCounter : public MainSolver {
public:
    MainCounter(std::unique_ptr<Theory> t, std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> th,
                std::unique_ptr<ModelCounter> ss, Logic & logic, SMTConfig & config, std::string && name)
                : MainSolver(std::move(t),
                             std::move(tm),
                             std::move(th),
                             std::move(ss),
                             logic,
                             config,
                             std::move(name))
    {}
    static std::unique_ptr<ModelCounter> createInnerSolver(SMTConfig & config, THandler & thandler) { return std::make_unique<ModelCounter>(config, thandler); }

    void countModels(vec<PTRef> const & terms);
};


#endif //OPENSMT_MAINCOUNTER_H
