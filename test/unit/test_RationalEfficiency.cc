//
// Created by prova on 23.11.20.
//

#include <gtest/gtest.h>
#include <Real.h>
#include <stdlib.h>
#include <Vec.h>
#include <chrono>
#include <Sort.h>

using Real = opensmt::Real;
using namespace std::chrono;

class RationalEfficiencyTest : public ::testing::Test {
    // INT32_MIN
    Real rmin {"-2147483648"};
    // INT32_MAX
    Real rmax {"2147493647"};

    Real bigmin = rmin*rmin*rmin;
    Real bigmax = rmax*rmax*rmax;

    class Timer {
        using Clock = high_resolution_clock;
        using tp = Clock::time_point;
        using OutDuration = milliseconds;
        tp start;
    public:
        Timer() : start(Clock::now()) {}

        ~Timer() {
            tp stop = Clock::now();
            auto diff = duration_cast<OutDuration>(stop - start);
            std::cout  << "Time elapsed: " << diff.count() << "ms\n";
        }
    };

public:
    void runBigNumTest(int rounds) const {
        Timer t;
        Real bg(bigmin);
        for (int i = 0; i < rounds; i++) {
            bg += 1;
        }
    }

    void runSmallNumTest(int rounds) const {
        Timer t;
        Real sn(rmin);
        for (int i = 0; i < rounds; i++) {
            sn += 1;
        }
    }

    void runSmallNumSumCommonUnity(int rounds) const {
        Timer t;
        Real a(1,3);
        Real b(1,5);
        for (int i = 0; i < rounds; i++) {
            Real c = a + b;
        }
    }

    void runSmallNumSumCommonNonUnity(int rounds) const {
        Timer t;
        Real a(1,3);
        Real b(1,6);
        for (int i = 0; i < rounds; i++) {
            Real c = a + b;
        }
    }

    void runSmallMulInv(int rounds) const {
        Timer t;
        Real a(13,29);
        Real b(29, 13);
        for (int i = 0; i < rounds; i++) {
            Real c = a * b;
        }
    }

    void runSmallMulNonInv(int rounds) const {
        Timer t;
        Real a(13,29);
        Real b(29, 7);
        for (int i = 0; i < rounds; i++) {
            Real c = a * b;
        }
    }
};

TEST_F(RationalEfficiencyTest, test_additionAssign)
{

    int rounds = 1000000;
    runBigNumTest(rounds);
    runSmallNumTest(rounds);

}

TEST_F(RationalEfficiencyTest, test_sumCommonUnity)
{
    int rounds = 1000000;
    runSmallNumSumCommonUnity(rounds);
    runSmallNumSumCommonNonUnity(rounds);
}

TEST_F(RationalEfficiencyTest, test_mulInverse)
{
    int rounds = 1000000;
    runSmallMulInv(rounds);
    runSmallMulNonInv(rounds);
}