//
// Created by prova on 23.11.20.
//

#include <benchmark/benchmark.h>
#include <Real.h>
#include <stdlib.h>
#include <Vec.h>
#include <chrono>
#include <Sort.h>
#include <iostream>

using Real = opensmt::Real;

class RationalEfficiencyFixture : public ::benchmark::Fixture {
protected:
    // INT32_MIN
    Real rmin {"-2147483648"};
    // INT32_MAX
    Real rmax {"2147493647"};

    Real bigmin = rmin*rmin*rmin;
    Real bigmax = rmax*rmax*rmax;

public:
    void SetUp(const ::benchmark::State& state) {
    }

    void TearDown(const ::benchmark::State& state) {
    }
};

BENCHMARK_F(RationalEfficiencyFixture, AdditionAssignBigMin)(benchmark::State& st) {
    Real bg(bigmin);
    for (auto _ : st)
        benchmark::DoNotOptimize(bg += 1);
}

BENCHMARK_F(RationalEfficiencyFixture, AdditionAssignSmallMin)(benchmark::State& st) {
    Real sn(rmin);
    for (auto _ : st)
        benchmark::DoNotOptimize(sn += 1);
}

BENCHMARK_F(RationalEfficiencyFixture, sumSmallCommonUnity)(benchmark::State& st) {
    Real a(1, 3);
    Real b(1, 5);
    Real c;
    for (auto _ : st) {
        c = a + b;
        benchmark::DoNotOptimize(c);
    }
}

BENCHMARK_F(RationalEfficiencyFixture, sumSmallCommonNonUnity)(benchmark::State& st) {
    Real a(1, 3);
    Real b(1, 6);
    Real c;
    for (auto _ : st) {
        c = a + b;
        benchmark::DoNotOptimize(c);
    }
}

BENCHMARK_F(RationalEfficiencyFixture, smallMulInv)(benchmark::State& st) {
    Real a(13, 29);
    Real b(29, 13);
    Real c;
    for (auto _ : st) {
        c = a * b;
        benchmark::DoNotOptimize(c);
    }
}

BENCHMARK_F(RationalEfficiencyFixture, smallMulNonInv)(benchmark::State& st) {
    Real a(13, 29);
    Real b(29, 7);
    Real c;
    for (auto _ : st) {
        c = a * b;
        benchmark::DoNotOptimize(c);
    }
}

BENCHMARK_F(RationalEfficiencyFixture, smallSumNegation)(benchmark::State& st) {
    int nom = 1;
    int den = 2;
    Real c;
    for (auto _ : st) {
        c = Real(nom, den) + Real(-nom, den);
        nom = (nom + 1) % INT32_MAX;
        den = std::max<int>(1, (den + 1) % INT32_MAX);
        benchmark::DoNotOptimize(c);
    }
}

BENCHMARK_F(RationalEfficiencyFixture, smallSubtractionEqual)(benchmark::State& st) {
    int nom = 1;
    int den = 2;
    Real c;
    for (auto _ : st) {
        c = Real(nom, den) - Real(nom, den);
        nom = (nom + 1) % INT32_MAX;
        den = std::max<int>(1, (den + 1) % INT32_MAX);
        benchmark::DoNotOptimize(c);
    }
}

BENCHMARK_F(RationalEfficiencyFixture, smallSum)(benchmark::State& st) {
    int nom = 1;
    int den = 2;
    Real c;
    for (auto _ : st) {
        c = Real(nom, den) + Real(nom, den);
        nom = (nom + 1) % INT32_MAX;
        den = std::max<int>(1, (den + 1) % INT32_MAX);
        benchmark::DoNotOptimize(c);
    }
}

BENCHMARK_F(RationalEfficiencyFixture, smallSubtraction)(benchmark::State& st) {
    int nom = 1;
    int den = 2;
    Real c;
    for (auto _ : st) {
        c = Real(nom, den) - Real(-nom, den);
        nom = (nom + 1) % INT32_MAX;
        den = std::max<int>(1, (den + 1) % INT32_MAX);
        benchmark::DoNotOptimize(c);
    }
}