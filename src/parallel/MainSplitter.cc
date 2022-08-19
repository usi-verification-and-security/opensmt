/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include "MainSplitter.h"
#include "VerificationUtils.h"

void MainSplitter::notifyResult(sstat const & result)
{
    if (result != s_Undef) {
        getChannel().setShallStop();
        getChannel().notify_all();
    }
}

sstat MainSplitter::check() {
    if (getChannel().isSolverInParallelMode() and not config.sat_solver_limit()) {
        //push frames size should match with length of the solver branch
        if (frames.size() !=
            static_cast<std::size_t>(getSplitter().getSolverBranch().size() + 1))
            throw PTPLib::common::Exception(__FILE__, __LINE__,
                                            ";assert: Inconsistency in push frames size and length of the solver address");
    }
    sstat res = MainSolver::check();
    notifyResult(res);
    status = res;
    return res;
}

sstat MainSplitter::solve_(vec<FrameId> & enabledFrames) {
    if (getChannel().isSolverInParallelMode() and not config.sat_solver_limit()) {
        vec<opensmt::pair<int, int>> const & solverBranch = getSplitter().getSolverBranch();
        if (enabledFrames.size() > solverBranch.size() + 1) {
            throw PTPLib::common::Exception(__FILE__, __LINE__,
                                            ";assert: inconsistency in solverBranch length and enabled_frame size: " +
                                            std::to_string(enabledFrames.size()) + " solverBranch size: " +
                                            std::to_string(solverBranch.size()));
        }
        for (int i = 0; i < enabledFrames.size(); i++) {
            if (i > 0)
                getSplitter().addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const>(solverBranch.begin(), i), enabledFrames[i].id);
        }
    }
    sstat res = MainSolver::solve_(enabledFrames);
    if (getSplitter().getSplits().size() >= 1 and res == s_False)
        throw PTPLib::common::Exception(__FILE__, __LINE__, ";assert: At least one split is created but splitter returned unsatisfiable.");
    return res;
}

sstat MainSplitter::solve() {
    sstat res = MainSolver::solve();
    if (getSplitter().getSplits().size() >= 1 and res == s_False)
        throw PTPLib::common::Exception(__FILE__, __LINE__, ";assert: At least one split is created but splitter returned unsatisfiable");
    return res;
};

void MainSplitter::writeSplits(std::string const & baseName) const {
    assert(config.sat_split_type() != spt_none);
    auto const & splits = getSplitter().getSplits();

    auto splitStrings = getPartitionClauses();
    int i = 0;
    for (auto const &splitString : splitStrings) {
        auto zeroPadNumber = [](int number, unsigned long targetLength) {
            std::string s = std::to_string(number);
            return std::string(targetLength - std::min(targetLength, s.length()), '0') + s;
        };

        std::string name = baseName + '-' + zeroPadNumber(i++, static_cast<int>(std::log10(splits.size()))+1) + ".smt2";
        std::ofstream outFile;
        outFile.open(name);
        if (outFile.is_open()) {
            outFile << "(assert " << splitString << ")\n";
            outFile.close();
        } else {
            throw OsmtApiException("Failed to open file " + name);
        }
    }
}

std::unique_ptr<SimpSMTSolver> MainSplitter::createInnerSolver(SMTConfig & config, THandler & thandler, PTPLib::net::Channel<PTPLib::net::SMTS_Event, PTPLib::net::Lemma> & ch) {
    if (config.sat_split_type() == spt_scatter) {
        return std::make_unique<ScatterSplitter>(config, thandler, ch);
    } else if (config.sat_split_type() == spt_lookahead) {
        return std::make_unique<LookaheadSplitter>(config, thandler, ch);
    } else {
        return MainSolver::createInnerSolver(config, thandler);
    }
}

std::vector<std::string> MainSplitter::getPartitionClauses() const {
    assert(not isSplitTypeNone());
    auto const & splits = getSplitter().getSplits();
    vec<PTRef> partitionsTr;
    partitionsTr.capacity(splits.size());
    for (auto const &split : splits) {
        auto conj_vec = addToConjunction(split.splitToPtAsgns(*thandler));
        partitionsTr.push(logic.mkAnd(conj_vec));
    }

    std::vector<std::string> partitions;
    for (PTRef trWithAuxVars : partitionsTr) {
        PTRef tr = logic.removeAuxVars(trWithAuxVars);
        partitions.push_back(logic.dumpWithLets(tr));
    }

    assert(
        [this](vec<PTRef> const & partitions) {
            bool ok = true;
            std::string error;
            VerificationUtils verifier(logic);
            for (int i = 0; i < partitions.size(); i++) {
                for (int j = i + 1; j < partitions.size(); j++) {
                    if (not verifier.impliesInternal(logic.mkAnd(partitions[i], partitions[j]), logic.getTerm_false())) {
                        error += "[Partitions share models: (and " + logic.pp(partitions[i]) + " " + logic.pp(partitions[j]) + ") is satisfiable] ";
                        ok = false;
                    }
                }
            }
            vec<PTRef> partitionCoverageQuery;
            partitionCoverageQuery.capacity(partitions.size());
            for (PTRef tr : partitions) {
                partitionCoverageQuery.push(logic.mkNot(tr));
            }
            if (partitions.size() == config.sat_split_num()) {
                // The partitions need to cover the full search space, i.e., the conjunction of the negated partitions must be unsatisfiable
                if (not verifier.impliesInternal(logic.mkAnd(partitionCoverageQuery), logic.getTerm_false())) {
                    error += "[Non-covering partitioning: " + logic.pp(logic.mkAnd(partitionCoverageQuery)) + " is satisfiable] ";
                    ok = false;
                }
            } else {
                // The partial partitioning must be satisfiable
                if (verifier.impliesInternal(logic.mkOr(partitions), logic.getTerm_false())) {
                    error += "[Unsatisfiable partial partitioning: " + logic.pp(logic.mkOr(partitions)) + "] ";
                    ok = false;
                } else {
                    // Removing the models of the partial partitions from the root instance must yield unsat
                    if (not verifier.impliesInternal(logic.mkAnd(partitionCoverageQuery), logic.mkNot(root_instance.getRoot()))) {
                        error += "[Non-covering partial partitioning: partial partitions do not contain all models of original instance] ";
                        ok = false;
                    }
                }
            }
            if (not ok) {
                std::cout << error << std::endl;
                throwWithLocationInfo(error);
            }
            return ok;
        }(partitionsTr)
    );

    return partitions;
}

vec<PTRef> MainSplitter::addToConjunction(std::vector<vec<PtAsgn>> const & in) const {
    vec<PTRef> out;
    for (const auto & constr : in) {
        vec<PTRef> disj_vec;
        for (const auto & pta : constr) {
            disj_vec.push(pta.sgn == l_True ? pta.tr : logic.mkNot(pta.tr));
        }
        out.push(logic.mkOr(std::move(disj_vec)));
    }
    return out;
}