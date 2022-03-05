/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "MainSplitter.h"
#include "LookaheadSplitter.h"
#include "SplitData.h"
#include "ScatterSplitter.h"
#include <cmath>

void MainSplitter::writeSplits(std::string const & baseName) const {
    assert(config.sat_split_type() != spt_none);
    assert(strcmp(config.output_dir(),"") != 0);

    std::vector<SplitData> const & splits = (config.sat_split_type() == spt_scatter)
            ? dynamic_cast<ScatterSplitter&>(ts.solver).getSplits()
            : dynamic_cast<LookaheadSplitter&>(ts.solver).getSplits();

    int i = 0;

    auto addToConjunction = [this](std::vector<vec<PtAsgn>> const & in, vec<PTRef> & out) {
        for (const auto & constr : in) {
            vec<PTRef> disj_vec;
            for (PtAsgn pta : constr)
                disj_vec.push(pta.sgn == l_True ? pta.tr : logic.mkNot(pta.tr));
            out.push(logic.mkOr(std::move(disj_vec)));
        }
    };

    for (auto const &split : splits) {
        vec<PTRef> conj_vec;

        addToConjunction(split.constraintsToPTRefs(*thandler), conj_vec);

        PTRef problem = logic.mkAnd(conj_vec);

        auto zeroPadNumber = [](int number, unsigned long targetLength) {
            std::string s = std::to_string(number);
            return std::string(targetLength - std::min(targetLength, s.length()), '0') + s;
        };

        std::string name = baseName + '-' + zeroPadNumber(i++, static_cast<int>(std::log10(splits.size()))+1) + ".smt2";
        std::ofstream outFile;
        outFile.open(name);
        if (outFile.is_open()) {
            logic.dumpFormulaToFile(outFile, problem);
            outFile.close();
        } else {
            throw OsmtApiException("Failed to open file " + name);
        }
    }
}

std::unique_ptr<SimpSMTSolver> MainSplitter::createInnerSolver(SMTConfig & config, THandler & thandler) {
    if (config.sat_split_type() == spt_scatter) {
        return std::make_unique<ScatterSplitter>(config, thandler);
    } else if (config.sat_split_type() == spt_lookahead) {
        return std::make_unique<LookaheadSplitter>(config, thandler);
    } else {
        return MainSolver::createInnerSolver(config, thandler);
    }
}

std::vector<std::string> MainSplitter::getPartitionClauses() {
    std::vector<std::string> partitions;
    std::vector<SplitData> const &splits = (config.sat_split_type() == spt_scatter)
                                           ? dynamic_cast<ScatterSplitter &>(ts.solver).getSplits()
                                           : dynamic_cast<LookaheadSplitter &>(ts.solver).getSplits();
    for (auto const &split : splits) {
        std::vector<vec<PtAsgn> > constraints;
        split.constraintsToPTRefs(*thandler);
        vec<PTRef> clauses;
        for (auto const &constraint : constraints) {
            vec<PTRef> clause;
            for (auto const &ptAsgn : constraint) {
                PTRef pt =
                        ptAsgn.sgn == l_True ?
                        ptAsgn.tr :
                        logic.mkNot(ptAsgn.tr);
                clause.push(pt);
            }
            clauses.push(logic.mkOr(clause));
        }
        partitions.push_back(logic.dumpWithLets(logic.mkAnd(clauses)));
    }
    return partitions;
}