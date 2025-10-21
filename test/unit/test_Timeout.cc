/*
 * Copyright (c) 2025, Kolarik Tomas <tomaqa@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

// Builds on "test_Stop.cc"

#include <gtest/gtest.h>

#include <api/MainSolver.h>
#include <logics/ArithLogic.h>

#include <array>
#include <future>
#include <thread>
#include <condition_variable>
#include <mutex>
#include <chrono>

// Pre-timeout checks if setting the time limit prior to solving works as expected
// Post-timeout checks if setting the time limit during solving works as expected

// Small pre-timeouts followed by large post-timeouts are unstable - we cannot anticipate preprocessing time
// These cases work only if the machine is fast enough - unusable for CI of user machines
// #define FAST_MACHINE

namespace opensmt {

std::mutex mutex;
std::condition_variable condVar;
size_t ackReadyCnt{0};
bool reqContinueFlag{false};

constexpr std::chrono::milliseconds computation_time_ms{30};
// Must be large enough to at least allow setting another consecutive time limit
constexpr std::chrono::milliseconds small_limit_ms{5};
// Must be large enough
constexpr std::chrono::milliseconds large_limit_ms{10000};

// Ensure that the computation takes more than small_limit_ms but less than large_limit_ms
static_assert(computation_time_ms >= small_limit_ms * 2);
static_assert(computation_time_ms * 10 <= large_limit_ms);

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

        std::this_thread::sleep_for(computation_time_ms);

        return MainSolver::solve_(enabledFrames);
    }
};

class TimeoutTest : public ::testing::Test {
public:

    ~TimeoutTest() {
        ackReadyCnt = 0;
        reqContinueFlag = false;
    }
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

    void setSmallTimeLimit(TestMainSolver & solver) {
        solver.setTimeLimit(small_limit_ms);
    }

    void setLargeTimeLimit(TestMainSolver & solver) {
        solver.setTimeLimit(large_limit_ms);
    }

    void setSmallTimeLimitAll() {
        for (size_t i = 0; i < nSolvers; ++i) {
            setSmallTimeLimit(solvers[i]);
        }
    }

    void setLargeTimeLimitAll() {
        for (size_t i = 0; i < nSolvers; ++i) {
            setLargeTimeLimit(solvers[i]);
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

TEST_F(TimeoutTest, test_NoTimeout) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(TimeoutTest, test_PreLargeTimeout) {
    init();

    setLargeTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(TimeoutTest, test_PreSmallTimeout) {
    init();

    setSmallTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

TEST_F(TimeoutTest, test_AllPreLargeTimeout) {
    init();

    setLargeTimeLimitAll();
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(TimeoutTest, test_AllPreSmallTimeout) {
    init();

    setSmallTimeLimitAll();
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(TimeoutTest, test_AllPreLargeThenOnePreLargeTimeout) {
    init();

    // also tests overriding already existing time limit thread
    setLargeTimeLimitAll();
    setLargeTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(TimeoutTest, test_AllPreLargeThenOnePreSmallTimeout) {
    init();

    // also tests overriding already existing time limit thread
    setLargeTimeLimitAll();
    setSmallTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

TEST_F(TimeoutTest, test_AllPreSmallThenOnePreLargeTimeout) {
    init();

    // also tests overriding already existing time limit thread
    setSmallTimeLimitAll();
    setLargeTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_Undef}));
}

TEST_F(TimeoutTest, test_AllPreSmallThenOnePreSmallTimeout) {
    init();

    // also tests overriding already existing time limit thread
    setSmallTimeLimitAll();
    setSmallTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

// Post-timeouts at least ensure the functionality of returning unknown after the solving is already trigerred

TEST_F(TimeoutTest, test_PostLargeTimeout) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    setLargeTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(TimeoutTest, test_PostSmallTimeout) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    setSmallTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

TEST_F(TimeoutTest, test_AllPostLargeTimeout) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    setLargeTimeLimitAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(TimeoutTest, test_AllPostSmallTimeout) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    setSmallTimeLimitAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(TimeoutTest, test_AllPostLargeThenOnePostLargeTimeout) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setLargeTimeLimitAll();
    setLargeTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(TimeoutTest, test_AllPostLargeThenOnePostSmallTimeout) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setLargeTimeLimitAll();
    setSmallTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

TEST_F(TimeoutTest, test_AllPostSmallThenOnePostLargeTimeout) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setSmallTimeLimitAll();
    setLargeTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_Undef}));
}

TEST_F(TimeoutTest, test_AllPostSmallThenOnePostSmallTimeout) {
    init();

    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setSmallTimeLimitAll();
    setSmallTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

// Combinations of pre- and post-timeouts

TEST_F(TimeoutTest, test_AllPreLargeThenOnePostLargeTimeout) {
    init();

    setLargeTimeLimitAll();
    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setLargeTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

TEST_F(TimeoutTest, test_AllPreLargeThenOnePostSmallTimeout) {
    init();

    setLargeTimeLimitAll();
    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setSmallTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_False}));
}

#ifdef FAST_MACHINE
TEST_F(TimeoutTest, test_AllPreSmallThenOnePostLargeTimeout) {
    init();

    setSmallTimeLimitAll();
    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setLargeTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_Undef}));
}
#endif

TEST_F(TimeoutTest, test_AllPreSmallThenOnePostSmallTimeout) {
    init();

    setSmallTimeLimitAll();
    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setSmallTimeLimit(solvers.front());
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(TimeoutTest, test_PreLargeThenAllPostLargeTimeout) {
    init();

    setLargeTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setLargeTimeLimitAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}

#ifdef FAST_MACHINE
TEST_F(TimeoutTest, test_PreSmallThenAllPostLargeTimeout) {
    init();

    setSmallTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setLargeTimeLimitAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_False, s_False}));
}
#endif

TEST_F(TimeoutTest, test_PreLargeThenAllPostSmallTimeout) {
    init();

    setLargeTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setSmallTimeLimitAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

TEST_F(TimeoutTest, test_PreSmallThenAllPostSmallTimeout) {
    init();

    setSmallTimeLimit(solvers.front());
    solveAllOnBackground();
    waitReadyAll();
    // also tests overriding already existing time limit thread
    setSmallTimeLimitAll();
    reqContinue();
    auto results = joinAll();

    ASSERT_EQ(results, std::to_array({s_Undef, s_Undef}));
}

} // namespace opensmt
