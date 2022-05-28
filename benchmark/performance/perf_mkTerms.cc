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

class MkTermsFixture : public ::benchmark::Fixture {
protected:


public:
    void SetUp(const ::benchmark::State&) {
    }

    void TearDown(const ::benchmark::State&) {
    }
};

BENCHMARK_F(MkTermsFixture, ManySmallConjunctions_OnlyPositive)(benchmark::State& st) {
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

BENCHMARK_F(MkTermsFixture, ManySmallConjunctions_OnlyNegative)(benchmark::State& st) {
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

BENCHMARK_F(MkTermsFixture, ManySmallConjunctions_Mixed)(benchmark::State& st) {
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

BENCHMARK_F(MkTermsFixture, OneLargeConjunctions_OnlyPositive)(benchmark::State& st) {
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

BENCHMARK_F(MkTermsFixture, OneLargeConjunctions_OnlyNegative)(benchmark::State& st) {
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

BENCHMARK_F(MkTermsFixture, OneLargeConjunctions_OnlyPositive_Randomized)(benchmark::State& st) {
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