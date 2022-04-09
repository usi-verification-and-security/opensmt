/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_MAINSPLITTER_H
#define OPENSMT_MAINSPLITTER_H

#include "MainSolver.h"
#include "ScatterSplitter.h"
#include "OsmtInternalException.h"

#include <PTPLib/net/Channel.hpp>

class MainSplitter : public MainSolver {
public:
    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig & config, THandler & thandler, PTPLib::net::Channel & ch);

    MainSplitter(std::unique_ptr<Theory> t,std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> th,
                 std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & config, std::string name)
                 :
                 MainSolver(std::move(t), std::move(tm), std::move(th), std::move(ss),logic,config, std::move(name))
                 {
                     if (not (dynamic_cast<ScatterSplitter&>(getSMTSolver())).getChannel().isSolverInParallelMode()) {
                         PTPLib::net::Header header = PTPLib::net::Header();
                         header.emplace(PTPLib::common::Param.NAME, config.getInstanceName());
                         header.emplace(PTPLib::common::Param.NODE, "[]");
                         (dynamic_cast<ScatterSplitter&>(getSMTSolver())).getChannel().set_current_header(header);
                     }
                 }

    std::vector<std::string> getPartitionClauses();
    void writeSplits(std::string const & file) const;

    sstat check() override {
        //push frames size should match with length of the solver branch
        if (frames.size() != (dynamic_cast<ScatterSplitter&>(getSMTSolver())).get_solver_branch().size() + 1) {
            throw OsmtInternalException("MainSplitter: Inconsistency in push frames size and length of the solver address");
        }
        return MainSolver::check();
    }

    void addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const> && solver_branch, uint32_t fid) {
        vec<opensmt::pair<int,int>> addrVector;
        addrVector.capacity(solver_branch.size());
        for (auto el : solver_branch) {
            addrVector.push(el);
        }
        this->term_mapper->mapSolverBranchToFrameId(fid, std::move(addrVector));
    }

    sstat solve_(vec<FrameId> & enabledFrames) override {
        vec<opensmt::pair<int,int>> const &  solverBranch = (dynamic_cast<ScatterSplitter&>(getSMTSolver())).get_solver_branch();
        for (int i = 0; i < enabledFrames.size(); i++) {
            if (enabledFrames.size() > solverBranch.size() + 1)
                throw OsmtInternalException(
                        "inconsistency in solverBranch length and enabled_frame size: " + std::to_string(enabledFrames.size()));
            if (i > 0) {
                addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const>(solverBranch.begin(), i), enabledFrames[i].id);
            }
        }
        return MainSolver::solve_(enabledFrames);
    }

    TermMapper& getTermMapper() { return *term_mapper;}
};


#endif //OPENSMT_MAINSPLITTER_H
