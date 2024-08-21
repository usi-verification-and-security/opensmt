//
// Created by Martin Blicha on 18.02.18.
//

#ifndef OPENSMT_NUMBER_H
#define OPENSMT_NUMBER_H

#include "Integer.h"
#include "Real.h"

#include <concepts>
#include <optional>

namespace opensmt {
// Should be compatible both with `Real` and `Integer`
using Number = Real;

static_assert(std::constructible_from<Number, Real>);
static_assert(std::constructible_from<Number, Integer>);

// TK: The current implementation assumes that Real can be directly and safely interpreted as Integer
// This preserves performance of the conversions
static_assert(std::derived_from<Integer, Real>);

inline bool isNegative(auto const & num) {
    return num.sign() < 0;
}

inline bool isPositive(auto const & num) {
    return num.sign() > 0;
}

inline bool isNonNegative(auto const & num) {
    return num.sign() >= 0;
}

inline bool isNonPositive(auto const & num) {
    return num.sign() <= 0;
}

//- inline Real getReal(Number const & num) noexcept {
//-     return num;
//- }
//- inline std::optional<Integer> tryGetInt(Number const & num) noexcept {
//-     if (num.isInteger()) return num;
//-     return {};
//- }
} // namespace opensmt

#endif // OPENSMT_NUMBER_H
