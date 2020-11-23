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

TEST(RationalEfficiency_test, test_division)
{
    // INT32_MIN
    Real rmin {"-2147483648"};
    // INT32_MAX
    Real rmax {"2147493647"};

    Real bigmin = rmin*rmin*rmin;
    Real bigmax = rmax*rmax*rmax;

    auto start = std::chrono::high_resolution_clock::now();
    auto stop 
}
