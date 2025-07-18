//
// Created by Tomaqa on 18.07.25
//

#include <gtest/gtest.h>

#include <api/MainSolver.h>
#include <logics/ArithLogic.h>

#include <chrono>
#include <future>
#include <thread>

using namespace std::chrono_literals;

namespace opensmt {

class StopTest : public ::testing::Test {
protected:
    void init() {
        PTRef x = logic.mkRealVar("x");
        PTRef y = logic.mkRealVar("y");
        PTRef z = logic.mkRealVar("z");
        PTRef w = logic.mkRealVar("w");
        PTRef v = logic.mkRealVar("v");

        solver.addAssertion(logic.mkOr(logic.mkEq(x, y), logic.mkEq(x, z)));

        solver.addAssertion(logic.mkOr(logic.mkEq(y, w), logic.mkEq(y, v)));
        solver.addAssertion(logic.mkOr(logic.mkEq(y, w), logic.mkEq(y, v)));

        solver.addAssertion(logic.mkOr(logic.mkEq(z, w), logic.mkEq(z, v)));
        solver.addAssertion(logic.mkOr(logic.mkEq(z, w), logic.mkEq(z, v)));

        solver.addAssertion(logic.mkLt(x, w));
        solver.addAssertion(logic.mkLt(x, v));
    }

    void runOnBackground(auto f) {
        std::packaged_task task{std::move(f)};
        future = task.get_future();
        thread = std::thread{std::move(task)};
    }

    void solveOnBackground() {
        runOnBackground([this] {
            std::this_thread::sleep_for(10ms);
            return solver.check();
        });
    }

    sstat wait() {
        thread.join();
        return future.get();
    }

    SMTConfig config{};
    ArithLogic logic{Logic_t::QF_LRA};
    MainSolver solver{logic, config, "solver"};

    std::thread thread;
    std::future<sstat> future;
};

TEST_F(StopTest, test_NoStop) {
    init();

    solveOnBackground();
    sstat result = wait();

    ASSERT_EQ(result, s_False);
}

TEST_F(StopTest, test_LocalPreStop) {
    init();

    solver.notifyStop();
    solveOnBackground();
    sstat result = wait();

    ASSERT_EQ(result, s_Undef);
}

TEST_F(StopTest, test_GlobalPreStop) {
    init();

    notifyGlobalStop();
    solveOnBackground();
    sstat result = wait();

    ASSERT_EQ(result, s_Undef);
}

TEST_F(StopTest, test_LocalPostStop) {
    init();

    solveOnBackground();
    std::this_thread::sleep_for(1ms);
    solver.notifyStop();
    sstat result = wait();

    ASSERT_EQ(result, s_Undef);
}

TEST_F(StopTest, test_GlobalPostStop) {
    init();

    solveOnBackground();
    std::this_thread::sleep_for(1ms);
    notifyGlobalStop();
    sstat result = wait();

    ASSERT_EQ(result, s_Undef);
}

TEST_F(StopTest, test_LocalTimeout) {
    init();

    solveOnBackground();
    if (future.wait_for(5ms) != std::future_status::timeout) {
        ASSERT_TRUE(false);
    }

    solver.notifyStop();
    sstat result = wait();

    ASSERT_EQ(result, s_Undef);
}

TEST_F(StopTest, test_GlobalTimeout) {
    init();

    solveOnBackground();
    if (future.wait_for(5ms) != std::future_status::timeout) {
        ASSERT_TRUE(false);
    }

    notifyGlobalStop();
    sstat result = wait();

    ASSERT_EQ(result, s_Undef);
}

} // namespace opensmt
