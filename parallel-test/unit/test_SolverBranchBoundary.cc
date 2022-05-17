/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#include <gtest/gtest.h>
#include <Logic.h>
#include <MainSplitter.h>
#include <PTPLib/net/Channel.hpp>

class SolverBranchBoundary : public ::testing::Test {
public:
    SolverBranchBoundary() : logic{opensmt::Logic_t::QF_UF} {}
    Logic logic;
    SMTConfig config;
};

TEST_F(SolverBranchBoundary, test_SolverBranch) {

    auto channel = std::make_unique<PTPLib::net::Channel>();
    auto th = MainSolver::createTheory(logic, config);
    auto tm = std::make_unique<TermMapper>(logic);
    auto thandler = new THandler(*th, *tm);
    std::unique_ptr<SimpSMTSolver> smt_solver = std::make_unique<ScatterSplitter>(config, *thandler, *channel);
    std::unique_ptr<MainSplitter> mainSplitter = std::make_unique<MainSplitter>(std::move(th),
                                          std::move(tm),
                                          std::unique_ptr<THandler>(thandler),
                                          std::move(smt_solver),
                                          logic,
                                          config,
                                          std::string("qf_uf")
                                          + " splitter");

    vec<Var> vars {
        var(mkLit(0, true)),
        var(mkLit(1, true)),
        var(mkLit(2, true)),
        var(mkLit(3, true)),
        var(mkLit(4, true)),
        var(mkLit(5, true)),
        var(mkLit(6, true)),
    };
    std::string solver_branch = std::string("0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1");
    (dynamic_cast<ScatterSplitter&>(mainSplitter->getSMTSolver())).set_solver_branch(solver_branch);

    vec<opensmt::pair<int, int>> const& solverBranch =
            (dynamic_cast<ScatterSplitter&>(mainSplitter->getSMTSolver())).get_solver_branch();

    for (int index = 0; index < vars.size(); ++index) {
        int span = index;
        int frameId = index + 1;
        (dynamic_cast<ScatterSplitter&>(mainSplitter->getSMTSolver())).addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const>(solverBranch.begin(), span), frameId);
        mainSplitter->getTermMapper().mapEnabledFrameIdToVar(vars[index], frameId);

        vec<opensmt::pair<int, int>> const & solverBranch_perVar = (dynamic_cast<ScatterSplitter &>(mainSplitter->getSMTSolver())).getSolverBranch(
                vars[index]);
        ASSERT_EQ(solverBranch_perVar.size(), span);
    }

}
