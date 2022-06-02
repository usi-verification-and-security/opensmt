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
    for (int i = 0; i < 50; ++i) {
        auto name = std::string("b") + std::to_string(i);
        vars.push_back(logic.mkBoolVar(name.c_str()));
    }

    for (auto _ : st) {
        for (auto i = 0u; i < vars.size(); ++i) {
            PTRef var1 = vars[i];
            for (auto j = 0u; j < vars.size(); ++j) {
                PTRef conj = logic.mkAnd(var1, vars[j]);
                benchmark::DoNotOptimize(conj);
            }
        }
    }
}

BENCHMARK_F(MkTerms, Neg)(benchmark::State& st) {
    Logic logic{opensmt::Logic_t::QF_UF};
    std::vector<PTRef> vars;
    for (int i = 0; i < 50; ++i) {
        auto name = std::string("b") + std::to_string(i);
        vars.push_back(logic.mkNot(logic.mkBoolVar(name.c_str())));
    }

    for (auto _ : st) {
        for (auto i = 0u; i < vars.size(); ++i) {
            PTRef var1 = vars[i];
            for (auto j = 0u; j < vars.size(); ++j) {
                PTRef conj = logic.mkAnd(var1, vars[j]);
                benchmark::DoNotOptimize(conj);
            }
        }
    }
}

BENCHMARK_F(MkTerms, Mix)(benchmark::State& st) {
    Logic logic{opensmt::Logic_t::QF_UF};
    std::vector<PTRef> vars;
    for (int i = 0; i < 25; ++i) {
        auto name = std::string("b") + std::to_string(i);
        vars.push_back(logic.mkBoolVar(name.c_str()));
    }

    for (int i = 0; i < 25; ++i) {
        vars.push_back(logic.mkNot(vars[i]));
    }

    for (auto _ : st) {
        for (auto i = 0u; i < vars.size(); ++i) {
            PTRef var1 = vars[i];
            for (auto j = 0u; j < vars.size(); ++j) {
                PTRef conj = logic.mkAnd(var1, vars[j]);
                benchmark::DoNotOptimize(conj);
            }
        }
    }
}
