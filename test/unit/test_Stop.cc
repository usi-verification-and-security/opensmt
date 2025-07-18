/*
 * Copyright (c) 2025, Kolarik Tomas <tomaqa@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include <gtest/gtest.h>

#include <api/GlobalStop.h>
#include <api/MainSolver.h>
#include <logics/ArithLogic.h>

#include <array>
#include <chrono>
#include <future>
#include <thread>

using namespace std::chrono_literals;

namespace opensmt {

constexpr auto const sleep_amount = 10ms;

class StopTest : public ::testing::Test {
protected:
    static constexpr size_t nSolvers = 2;

    void init() {
        for (size_t i = 0; i < nSolvers; ++i) {
            auto & logic = logics[i];
            auto & solver = solvers[i];

            PTRef x = logic.mkRealVar("x");
            PTRef y = logic.mkRealVar("y");
            PTRef z = logic.mkRealVar("z");
            PTRef w = logic.mkRealVar("w");
            PTRef v = logic.mkRealVar("v");

            // This at least ensures that it is not solved just during the preprocessing phase

            solver.addAssertion(logic.mkOr(logic.mkEq(x, y), logic.mkEq(x, z)));
            solver.addAssertion(logic.mkOr(logic.mkEq(y, w), logic.mkEq(y, v)));
            solver.addAssertion(logic.mkOr(logic.mkEq(z, w), logic.mkEq(z, v)));

            solver.addAssertion(logic.mkLt(x, w));
            solver.addAssertion(logic.mkLt(x, v));
        }
    }

    void solveAllOnBackground() {
        for (size_t i = 0; i < nSolvers; ++i) {
            solveOnBackground(i);
        }
    }

    void notifyAll() {
        for (size_t i = 0; i < nSolvers; ++i) {
            solvers[i].notifyStop();
        }
    }

    std::array<sstat, nSolvers> waitAll() {
        std::array<sstat, nSolvers> results;
        for (size_t i = 0; i < nSolvers; ++i) {
            results[i] = wait(i);
        }
        return results;
    }

    SMTConfig config{};
    std::array<ArithLogic, nSolvers> logics{Logic_t::QF_LRA, Logic_t::QF_LRA};
    std::array<MainSolver, nSolvers> solvers{MainSolver{logics[0], config, "solver 1"},
                                             MainSolver{logics[1], config, "solver 2"}};

    std::array<std::thread, nSolvers> threads;
    std::array<std::future<sstat>, nSolvers> futures;

private:
    void runOnBackground(size_t idx, auto f) {
        std::packaged_task task{std::move(f)};
        futures[idx] = task.get_future();
        threads[idx] = std::thread{std::move(task)};
    }

    void solveOnBackground(size_t idx) {
        runOnBackground(idx, [this, idx] {
            std::this_thread::sleep_for(sleep_amount);
            return solvers[idx].check();
        });
    }

    sstat wait(size_t idx) {
        threads[idx].join();
        return futures[idx].get();
    }
};

TEST_F(StopTest, test_NoStop) {
    init();

    solveAllOnBackground();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(StopTest, test_LocalPreStop) {
    init();

    solvers.front().notifyStop();
    solveAllOnBackground();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

TEST_F(StopTest, test_GlobalPreStop) {
    init();

    notifyGlobalStop();
    solveAllOnBackground();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(StopTest, test_AllLocalPreStop) {
    init();

    notifyAll();
    solveAllOnBackground();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

// Post-stops at least ensure the functionality of returning unknown after the solving is already trigerred

TEST_F(StopTest, test_LocalPostStop) {
    init();

    solveAllOnBackground();
    std::this_thread::sleep_for(sleep_amount / 10);
    solvers.front().notifyStop();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

TEST_F(StopTest, test_GlobalPostStop) {
    init();

    solveAllOnBackground();
    std::this_thread::sleep_for(sleep_amount / 10);
    notifyGlobalStop();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(StopTest, test_AllLocalPostStop) {
    init();

    solveAllOnBackground();
    std::this_thread::sleep_for(sleep_amount / 10);
    notifyAll();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(StopTest, test_LocalTimeout) {
    init();

    solveAllOnBackground();
    if (futures.front().wait_for(sleep_amount / 2) != std::future_status::timeout) { ASSERT_TRUE(false); }

    solvers.front().notifyStop();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

TEST_F(StopTest, test_GlobalTimeout) {
    init();

    solveAllOnBackground();
    if (futures.front().wait_for(sleep_amount / 2) != std::future_status::timeout) { ASSERT_TRUE(false); }

    notifyGlobalStop();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(StopTest, test_AllLocalTimeout) {
    init();

    solveAllOnBackground();
    if (futures.front().wait_for(sleep_amount / 2) != std::future_status::timeout) { ASSERT_TRUE(false); }

    notifyAll();
    auto results = waitAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

} // namespace opensmt
