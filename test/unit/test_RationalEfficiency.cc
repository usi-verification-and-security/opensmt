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

class RationalEfficiencyTest : public ::testing::Test {
    // INT32_MIN
    Real rmin {"-2147483648"};
    // INT32_MAX
    Real rmax {"2147493647"};

    Real bigmin = rmin*rmin*rmin;
    Real bigmax = rmax*rmax*rmax;

    class Timer {
        using duration = std::chrono::duration<double>;
        using tp = std::chrono::time_point<std::chrono::steady_clock,duration>;
        tp start;
    public:
        Timer() : start(std::chrono::high_resolution_clock::now()) {}
        ~Timer() {
            tp stop = std::chrono::high_resolution_clock::now();
            duration diff = stop - start;
            std::cout  << "Time elapsed: " << diff.count() << "s\n";
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
};

TEST_F(RationalEfficiencyTest, test_division)
{

    int rounds = 10000000;
    runBigNumTest(rounds);
    runSmallNumTest(rounds);

}
