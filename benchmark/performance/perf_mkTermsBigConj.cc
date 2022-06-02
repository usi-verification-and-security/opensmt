/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */
#include <benchmark/benchmark.h>
#include <Logic.h>

#include <algorithm>
#include <random>

class MkTerms : public ::benchmark::Fixture {
protected:


public:
    void SetUp(const ::benchmark::State&) {
    }

    void TearDown(const ::benchmark::State&) {
    }
};

BENCHMARK_F(MkTerms, Pos)(benchmark::State& st) {
    Logic logic{opensmt::Logic_t::QF_UF};
    std::vector<PTRef> vars;
    for (int i = 0; i < 100; ++i) {
        auto name = std::string("b") + std::to_string(i);
        vars.push_back(logic.mkBoolVar(name.c_str()));
    }

    vec<PTRef> args = vars;
    for (auto _ : st) {
        PTRef conj = logic.mkAnd(args);
        benchmark::DoNotOptimize(conj);
    }
}

BENCHMARK_F(MkTerms, Neg)(benchmark::State& st) {
    Logic logic{opensmt::Logic_t::QF_UF};
    std::vector<PTRef> vars;
    for (int i = 0; i < 100; ++i) {
        auto name = std::string("b") + std::to_string(i);
        vars.push_back(logic.mkBoolVar(name.c_str()));
    }

    vec<PTRef> args;
    args.capacity(vars.size());
    for (PTRef var : vars) {
        args.push(logic.mkNot(var));
    }

    for (auto _ : st) {
        PTRef conj = logic.mkAnd(args);
        benchmark::DoNotOptimize(conj);
    }
}

BENCHMARK_F(MkTerms, PosRand)(benchmark::State& st) {
    Logic logic{opensmt::Logic_t::QF_UF};
    std::vector<PTRef> vars;
    for (int i = 0; i < 100; ++i) {
        auto name = std::string("b") + std::to_string(i);
        vars.push_back(logic.mkBoolVar(name.c_str()));
    }
    vec<PTRef> args = vars;
    std::shuffle(args.begin(), args.end(), std::default_random_engine(0));

    for (auto _ : st) {
        PTRef conj = logic.mkAnd(args);
        benchmark::DoNotOptimize(conj);
    }
}