/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_MAINSPLITTER_HPP
#define OPENSMT_MAINSPLITTER_HPP

#include "MainSolver.h"
#include "SplitData.h"
#include <cmath>
#ifdef CUBE_AND_CONQUER
    #include "ParallelScatterSplitter.h"
#else
    #include "ScatterSplitter.h"
#endif
#include "OsmtInternalException.h"
#include "LookaheadSplitter.h"
#include "Splitter.h"

class MainSplitter : public MainSolver {
public:

    bool isSplitTypeScatter() const { return config.sat_split_type() == spt_scatter; }

    MainSplitter(std::unique_ptr<Theory> t,std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> th,
                 std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & config, std::string name)
                 :
                 MainSolver(std::move(t), std::move(tm), std::move(th), std::move(ss),logic,config, std::move(name))
                 {
#ifdef CUBE_AND_CONQUER
                     if (isSplitTypeScatter())
                         if (not (dynamic_cast<ParallelScatterSplitter&>(getSMTSolver())).getChannel().isSolverInParallelMode()) {
                             PTPLib::net::Header header = PTPLib::net::Header();
                             header.emplace(PTPLib::common::Param.NAME, config.getInstanceName());
                             header.emplace(PTPLib::common::Param.NODE, "[]");
                             (dynamic_cast<ParallelScatterSplitter&>(getSMTSolver())).getChannel().set_current_header(header);
                         }
#endif
                 }

#ifdef CUBE_AND_CONQUER
    sstat check() override {
        //push frames size should match with length of the solver branch
        if (isSplitTypeScatter())
            if (frames.size() != static_cast<std::size_t>((dynamic_cast<ParallelScatterSplitter&>(getSMTSolver())).get_solver_branch().size() + 1))
                throw PTPLib::common::Exception(__FILE__, __LINE__,";assert: Inconsistency in push frames size and length of the solver address");

        return MainSolver::check();
    }

    sstat solve_(vec<FrameId> & enabledFrames) override {
        if (isSplitTypeScatter()) {
            vec<opensmt::pair<int, int>> const & solverBranch = (dynamic_cast<ParallelScatterSplitter &>(getSMTSolver())).get_solver_branch();
            for (int i = 0; i < enabledFrames.size(); i++) {
                if (enabledFrames.size() > solverBranch.size() + 1)
                    throw PTPLib::common::Exception(__FILE__, __LINE__,
                                                    ";assert: inconsistency in solverBranch length and enabled_frame size: " +
                                                    std::to_string(enabledFrames.size()));
                if (i > 0) {
                    (dynamic_cast<ParallelScatterSplitter&>(getSMTSolver())).addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const>(solverBranch.begin(), i), enabledFrames[i].id);
                }
            }
        }
        return MainSolver::solve_(enabledFrames);
    }
#endif
    void writeSplits(std::string const & baseName) const {
        assert(config.sat_split_type() != spt_none);
        assert(strcmp(config.output_dir(),"") != 0);

        std::vector<SplitData> const & splits = dynamic_cast<Splitter&>(ts.solver).getSplits();

        int i = 0;
        auto addToConjunction = [this](std::vector<vec<PtAsgn>> const & in) {
            vec<PTRef> out;
            for (const auto & constr : in) {
                vec<PTRef> disj_vec;
                for (PtAsgn pta : constr)
                    disj_vec.push(pta.sgn == l_True ? pta.tr : logic.mkNot(pta.tr));
                out.push(logic.mkOr(std::move(disj_vec)));
            }
            return out;
        };

        for (auto const &split : splits) {
            vec<PTRef> conj_vec = addToConjunction(split.constraintsToPTRefs(*thandler));

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

    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig & config, THandler & thandler) {
        if (config.sat_split_type() == spt_scatter) {
#ifdef CUBE_AND_CONQUER
            return std::make_unique<ParallelScatterSplitter>(config, thandler);
#else
            return std::make_unique<ScatterSplitter>(config, thandler);
#endif

        } else if (config.sat_split_type() == spt_lookahead) {
            return std::make_unique<LookaheadSplitter>(config, thandler);
        } else {
            return MainSolver::createInnerSolver(config, thandler);
        }
    }

    std::vector<std::string> getPartitionClauses() {
        std::vector<std::string> partitions;
        std::vector<SplitData> const & splits = dynamic_cast<Splitter&>(ts.solver).getSplits();
        for (auto const &split : splits) {
            std::vector<vec<PtAsgn>> constraints;
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

    TermMapper& getTermMapper() { return *term_mapper;}
};


#endif //OPENSMT_MAINSPLITTER_HPP
