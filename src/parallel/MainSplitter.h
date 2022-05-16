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
#include "ScatterSplitter.h"
#include "OsmtInternalException.h"
#include "LookaheadSplitter.h"
#include "Splitter.h"

#include <cmath>

class MainSplitter : public MainSolver {
public:

    bool isSplitTypeScatter() const & { return dynamic_cast<Splitter&>(ts.solver).isSplitTypeScatter(); }

    bool isSplitTypeNone() const & { return dynamic_cast<Splitter&>(ts.solver).isSplitTypeNone(); }

    MainSplitter(std::unique_ptr<Theory> t,std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> th,
                 std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & config, std::string name)
                 :
                 MainSolver(std::move(t), std::move(tm), std::move(th), std::move(ss),logic,config, std::move(name))
                 {}

    PTPLib::net::Channel & getChannel()  { return (dynamic_cast<ScatterSplitter&>(getSMTSolver())).getChannel(); }

    void notifyResult(sstat const & result)
    {
        if (result != s_Undef) {
            getChannel().setShallStop();
            getChannel().notify_all();
        }
    }

    sstat check() override {
        if (not config.sat_solver_limit())
        //push frames size should match with length of the solver branch
            if (frames.size() != static_cast<std::size_t>((dynamic_cast<ScatterSplitter&>(getSMTSolver())).get_solver_branch().size() + 1))
                throw PTPLib::common::Exception(__FILE__, __LINE__,";assert: Inconsistency in push frames size and length of the solver address");

        sstat res = MainSolver::check();
        notifyResult(res);
        status = res;
        return res;
    }

    sstat solve_(vec<FrameId> & enabledFrames) override {
        if (not config.sat_solver_limit()) {
            vec<opensmt::pair<int, int>> const & solverBranch = (dynamic_cast<ScatterSplitter &>(getSMTSolver())).get_solver_branch();
            for (int i = 0; i < enabledFrames.size(); i++) {
                if (enabledFrames.size() > solverBranch.size() + 1)
                    throw PTPLib::common::Exception(__FILE__, __LINE__,
                                                    ";assert: inconsistency in solverBranch length and enabled_frame size: " +
                                                    std::to_string(enabledFrames.size()) + " solverBranch size: " +
                                                    std::to_string(solverBranch.size()));
                if (i > 0) {
                    (dynamic_cast<ScatterSplitter &>(getSMTSolver())).addBranchToFrameId(
                            opensmt::span<opensmt::pair<int, int> const>(solverBranch.begin(), i), enabledFrames[i].id);
                }
            }
        }
        sstat res = MainSolver::solve_(enabledFrames);
        if (dynamic_cast<Splitter&>(ts.solver).getSplits().size() >= 1 and res == s_False)
            throw PTPLib::common::Exception(__FILE__, __LINE__, ";assert: At least one split is created and while conflict encountered!");
        return res;
    }


    sstat solve() {
        sstat res = MainSolver::solve();
        if (dynamic_cast<Splitter&>(ts.solver).getSplits().size() >= 1 and res == s_False)
            throw PTPLib::common::Exception(__FILE__, __LINE__, ";assert: At least one split is created and while conflict encountered!");
        return res;
    };

    void writeSplits(std::string const & baseName) const {
        assert(config.sat_split_type() != spt_none);
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

    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig & config, THandler & thandler, PTPLib::net::Channel & ch) {
        if (config.sat_split_type() == spt_scatter) {
            return std::make_unique<ScatterSplitter>(config, thandler, ch);
        } else if (config.sat_split_type() == spt_lookahead) {
            return std::make_unique<LookaheadSplitter>(config, thandler);
        } else {
            return MainSolver::createInnerSolver(config, thandler);
        }
    }

    std::vector<std::string> getPartitionClauses() {
        assert(not isSplitTypeNone());
        std::vector<std::string> partitions;
        std::vector<SplitData> const & splits = dynamic_cast<Splitter&>(ts.solver).getSplits();
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
            partitions.push_back(logic.dumpWithLets(problem));
        }
        return partitions;
    }

    TermMapper& getTermMapper() { return *term_mapper;}
};


#endif //OPENSMT_MAINSPLITTER_HPP
