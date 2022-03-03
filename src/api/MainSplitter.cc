/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include <LookaheadSplitter.h>
#include "MainSplitter.h"
#include "SplitData.h"
#include "ScatterSplitter.h"
#include <filesystem>

void MainSplitter::writeSolverSplits_smtlib2(std::string const & baseName) const {
    if (config.sat_split_type() != spt_none and dynamic_cast<ScatterSplitter&>(ts.solver).getSplitConfig_split_on()
    and strcmp(config.output_dir(),"") != 0) {
        std::vector<SplitData> const &splits = (config.sat_split_type() == spt_scatter)
                                               ? dynamic_cast<ScatterSplitter &>(ts.solver).getSplits()
                                               : dynamic_cast<LookaheadSplitter &>(ts.solver).getSplits();
        int i = 0;
        std::cout << config.sat_split_num() << std::endl;
        std::cout << splits.size() << std::endl;
        std::filesystem::create_directory(config.output_dir());
        auto addToConjunction = [this](std::vector<vec<PtAsgn>> const &in, vec<PTRef> &out) {
            for (const auto &constr : in) {
                vec<PTRef> disj_vec;
                for (PtAsgn pta : constr)
                    disj_vec.push(pta.sgn == l_True ? pta.tr : logic.mkNot(pta.tr));
                out.push(logic.mkOr(std::move(disj_vec)));
            }
        };

        for (auto const &split : splits) {
            vec<PTRef> conj_vec;

            addToConjunction(split.constraintsToPTRefs(*thandler), conj_vec);
            addToConjunction(split.learntsToPTRefs(*thandler), conj_vec);

            if (config.smt_split_format_length() == spformat_full)
                conj_vec.push(root_instance.getRoot());

            PTRef problem = logic.mkAnd(conj_vec);

            auto zeroPadString = [](std::string const &s, unsigned long nZeros) {
                return std::string(nZeros - std::min(nZeros, s.length()), '0') + s;
            };

            std::string name = baseName + '-' + zeroPadString(std::to_string(i++), 2) + ".smt2";
            std::ofstream outFile;
            outFile.open(name);
            if (outFile.is_open()) {
                logic.dumpHeaderToFile(outFile);
                logic.dumpFormulaToFile(outFile, problem);

                if (config.smt_split_format_length() == spformat_full)
                    logic.dumpChecksatToFile(outFile);

                outFile.close();
            } else {
                throw OsmtApiException("Failed to open file " + name);
            }
        }
    }
}
