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
#include <future>
#include <thread>
#include <condition_variable>
#include <mutex>

namespace opensmt {

std::mutex mutex;
std::condition_variable condVar;
size_t ackReadyCnt{0};
bool reqContinueFlag{false};

class TestMainSolver : public MainSolver {
public:
    using MainSolver::MainSolver;

protected:
    sstat solve_(vec<FrameId> const & enabledFrames) override {
        std::unique_lock lock(mutex);
        ++ackReadyCnt;
        lock.unlock();
        condVar.notify_all();
        lock.lock();
        condVar.wait(lock, []{ return reqContinueFlag; });
        lock.unlock();

        return MainSolver::solve_(enabledFrames);
    }
};

class StopTest : public ::testing::Test {
public:

    ~StopTest() {
        resetGlobalStop();

        ackReadyCnt = 0;
        reqContinueFlag = false;
    }
protected:
    static constexpr size_t nSolvers = 2;

    void init() {
        assert(not globallyStopped());

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

    void waitReadyAll() {
        std::unique_lock lock(mutex);
        condVar.wait(lock, []{ return ackReadyCnt == nSolvers; });
    }

    void reqContinue() {
        {
            std::lock_guard lock(mutex);
            reqContinueFlag = true;
        }
        condVar.notify_all();
    }

    void notifyStopAll() {
        for (size_t i = 0; i < nSolvers; ++i) {
            solvers[i].notifyStop();
        }
    }

    std::array<sstat, nSolvers> joinAll() {
        std::array<sstat, nSolvers> results;
        for (size_t i = 0; i < nSolvers; ++i) {
            results[i] = join(i);
        }
        return results;
    }

    SMTConfig config{};
    std::array<ArithLogic, nSolvers> logics{Logic_t::QF_LRA, Logic_t::QF_LRA};
    std::array<TestMainSolver, nSolvers> solvers{TestMainSolver{logics[0], config, "solver 1"},
                                                 TestMainSolver{logics[1], config, "solver 2"}};

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
            return solvers[idx].check();
        });
    }

    sstat join(size_t idx) {
        threads[idx].join();
        return futures[idx].get();
    }
};

TEST_F(StopTest, test_NoStop) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(StopTest, test_LocalPreStop) {
    init();

    solvers.front().notifyStop();
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

TEST_F(StopTest, test_GlobalPreStop) {
    init();

    notifyGlobalStop();
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(StopTest, test_AllLocalPreStop) {
    init();

    notifyStopAll();
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

// Post-stops at least ensure the functionality of returning unknown after the solving is already trigerred

TEST_F(StopTest, test_LocalPostStop) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    solvers.front().notifyStop();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

TEST_F(StopTest, test_GlobalPostStop) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    notifyGlobalStop();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(StopTest, test_AllLocalPostStop) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    notifyStopAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

} // namespace opensmt
