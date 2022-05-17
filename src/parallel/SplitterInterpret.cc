/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SplitterInterpret.h"

/***********************************************************
 * Class defining Splitter-Interpreter
 * Usage: Parallel solver
 ***********************************************************/

void SplitterInterpret::writeSplits(const char* filename)
{
    try {
        dynamic_cast<MainSplitter &>(getMainSolver()).writeSplits(filename);
    }
    catch (OsmtApiException const & e) {
        std::cout << "While writing splits: " << e.what() << std::endl;
    }
}

sstat SplitterInterpret::checkSat() {
    char* name = config.dump_state();
    sstat res = Interpret::checkSat();
    if (res == s_Undef and strcmp(config.output_dir(),"") != 0) {
        writeSplits(name);
    }
    return res;
}

std::unique_ptr<MainSolver> SplitterInterpret::createMainSolver(const char* logic_name) {
    assert(config.sat_split_type() != spt_none);
    auto th = MainSolver::createTheory(*logic, config);
    auto tm = std::make_unique<TermMapper>(*logic);
    auto thandler = new THandler(*th, *tm);
    return std::make_unique<MainSplitter>(std::move(th),
                             std::move(tm),
                             std::unique_ptr<THandler>(thandler),
                             MainSplitter::createInnerSolver(config, *thandler, channel),
                             *logic,
                             config,
                             std::string(logic_name)
                             + " splitter");
}



