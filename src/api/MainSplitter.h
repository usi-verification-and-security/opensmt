/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_MAINSPLITTER_H
#define OPENSMT_MAINSPLITTER_H

#include "MainSolver.h"

class MainSplitter : public MainSolver {

public:
    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig & config, THandler & thandler);

    MainSplitter(std::unique_ptr<Theory> t,std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> th,
                 std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & config, std::string name)
                 :
                 MainSolver(std::move(t), std::move(tm), std::move(th), std::move(ss),logic,config, std::move(name))
                 {}

    void writeSolverSplits_smtlib2(std::string const & file) const;
};


#endif //OPENSMT_MAINSPLITTER_H
