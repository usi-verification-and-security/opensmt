//
// Created by Martin Blicha on 18.02.18.
//

#ifndef OPENSMT_NUMBER_H
#define OPENSMT_NUMBER_H

#include "Integer.h"
#include "NumberConcept.h"
#include "Real.h"

#include <common/FunUtils.h>
#include <common/TypeUtils.h>

#include <cassert>
#include <compare>
#include <concepts>
#include <functional>
#include <iosfwd>
#include <optional>
#include <string>
#include <utility>
#include <variant>

namespace opensmt {
class StrictNumber : public std::variant<Integer, Real> {
public:
    struct Hash {
        std::size_t operator()(StrictNumber const & n) const { return n.hash(); }
    };

    using variant::variant;
    // No constructors from non-class values

    bool isInteger() const noexcept { return std::holds_alternative<Integer>(*this); }
    bool isReal() const noexcept { return std::holds_alternative<Real>(*this); }

    Integer const * tryGetInteger() const noexcept { return std::get_if<Integer>(this); }
    Integer * tryGetInteger() noexcept { return std::get_if<Integer>(this); }
    Real const * tryGetReal() const noexcept { return std::get_if<Real>(this); }
    Real * tryGetReal() noexcept { return std::get_if<Real>(this); }

    int sign() const {
        return std::visit([](auto & x) { return x.sign(); }, *this);
    }

    bool isZero() const {
        return std::visit([](auto & x) { return x.isZero(); }, *this);
    }
    bool isOne() const {
        return std::visit([](auto & x) { return x.isOne(); }, *this);
    }
    bool isIntegerValue() const {
        return std::visit([](auto & x) { return x.isIntegerValue(); }, *this);
    }

    bool operator==(StrictNumber const & rhs) const { return std::is_eq(operator<=>(rhs)); }
    std::strong_ordering operator<=>(StrictNumber const & rhs) const { return compareTp(rhs); }

    StrictNumber operator+(StrictNumber const & rhs) const { return arithOperatorTp<std::plus<void>>(rhs); }
    StrictNumber operator-(StrictNumber const & rhs) const { return arithOperatorTp<std::minus<void>>(rhs); }
    StrictNumber operator*(StrictNumber const & rhs) const { return arithOperatorTp<std::multiplies<void>>(rhs); }
    StrictNumber operator/(StrictNumber const & rhs) const { return arithOperatorTp<std::divides<void>>(rhs); }
    StrictNumber & operator+=(StrictNumber const & rhs) { return arithAssignOperatorTp<std::plus<void>>(rhs); }
    StrictNumber & operator-=(StrictNumber const & rhs) { return arithAssignOperatorTp<std::minus<void>>(rhs); }
    StrictNumber & operator*=(StrictNumber const & rhs) { return arithAssignOperatorTp<std::multiplies<void>>(rhs); }
    StrictNumber & operator/=(StrictNumber const & rhs) { return arithAssignOperatorTp<std::divides<void>>(rhs); }
    StrictNumber operator+(std::integral auto val) const { return arithOperatorTp<std::plus<void>>(val); }
    StrictNumber operator-(std::integral auto val) const { return arithOperatorTp<std::minus<void>>(val); }
    StrictNumber operator*(std::integral auto val) const { return arithOperatorTp<std::multiplies<void>>(val); }
    StrictNumber operator/(std::integral auto val) const { return arithOperatorTp<std::divides<void>>(val); }
    StrictNumber & operator+=(std::integral auto val) { return arithAssignOperatorTp<std::plus<void>>(val); }
    StrictNumber & operator-=(std::integral auto val) { return arithAssignOperatorTp<std::minus<void>>(val); }
    StrictNumber & operator*=(std::integral auto val) { return arithAssignOperatorTp<std::multiplies<void>>(val); }
    StrictNumber & operator/=(std::integral auto val) { return arithAssignOperatorTp<std::divides<void>>(val); }

    StrictNumber ceil() const { return ceilTp(); }
    StrictNumber floor() const { return floorTp(); }

    StrictNumber & negate() { return negateTp(); }
    StrictNumber & reset() noexcept { return resetTp(); }

    std::optional<Integer> tryMakeInteger() const {
        using Ret = std::optional<Integer>;
        return std::visit(Overload{
                              [](Integer const & x) -> Ret { return x; },
                              [](Real const & x) { return tryMakeInteger(x); },
                          },
                          *this);
    }

    Real makeReal() const {
        return std::visit([](auto & x) -> Real { return x; }, *this);
    }

    bool tryTurnToInteger() {
        return std::visit(Overload{
                              [](Integer & x) { return true; },
                              [this](Real & x) { return tryTurnToInteger(x); },
                          },
                          *this);
    }

    void turnToReal() {
        return std::visit(Overload{
                              [this](Integer & x) { emplace<Real>(std::move(x)); },
                              [](Real & x) {},
                          },
                          *this);
    }

    std::string toString() const {
        return std::visit([](auto & x) { return x.toString(); }, *this);
    }
    void print(std::ostream & os) const {
        std::visit([&os](auto & x) { return x.print(os); }, *this);
    }

    std::size_t hash() const {
        return std::visit([](auto & x) { return x.hash(); }, *this);
    }

protected:
    // The following functions currently make this assumption
    static_assert(std::derived_from<Integer, Real>);

    template<typename T>
    std::strong_ordering compareTp(T const & rhs) const {
        constexpr bool const isStrict = std::is_same_v<T, StrictNumber>;
        return intToOrdering(std::visit(
            []<typename U, typename V>(U const & x, V const & y) {
                if constexpr (std::is_same_v<U, V>) {
                    return x.compare(y);
                } else if constexpr (isStrict) {
                    // if strict, then using distinct arguments is UB
                    assert(false);
                    return 1;
                } else {
                    return static_cast<Real const &>(x).compare(static_cast<Real const &>(y));
                }
            },
            *this, rhs));
    }

    template<typename Op, typename T>
    T arithOperatorTp(T const & rhs) const {
        constexpr bool const isStrict = std::is_same_v<T, StrictNumber>;
        return std::visit(
            []<typename U, typename V>(U const & x, V const & y) -> T {
                if constexpr (std::is_same_v<U, V>) {
                    return Op{}(x, y);
                } else if constexpr (isStrict) {
                    // if strict, then using distinct arguments is UB
                    assert(false);
                    return {};
                } else {
                    return Op{}(static_cast<Real const &>(x), static_cast<Real const &>(y));
                }
            },
            *this, rhs);
    }

    template<typename Op, typename T>
    T & arithAssignOperatorTp(T const & rhs) {
        using AssignOp = CompoundAssignOf<Op>;
        constexpr bool const isStrict = std::is_same_v<T, StrictNumber>;
        constexpr bool const isDiv = std::is_same_v<Op, std::divides<void>>;
        std::visit(
            []<typename U, typename V>(U & x, V const & y) {
                if constexpr (std::is_same_v<U, V> and (not isDiv or std::is_same_v<U, Real>)) {
                    AssignOp{}(x, y);
                } else if constexpr (isStrict or (isDiv and not std::is_same_v<U, Real>)) {
                    // if strict, then using distinct arguments is UB
                    // or if dividing and lhs is not real
                    assert(false);
                } else {
                    AssignOp{}(static_cast<Real &>(x), static_cast<Real const &>(y));
                }
            },
            *this, rhs);

        return static_cast<T &>(*this);
    }

    template<typename Op, typename T = StrictNumber>
    T arithOperatorTp(std::integral auto val) const {
        return std::visit([val](auto & x) -> T { return Op{}(x, val); }, *this);
    }

    template<typename Op, typename T = StrictNumber>
    T & arithAssignOperatorTp(std::integral auto val) {
        using AssignOp = CompoundAssignOf<Op>;
        constexpr bool const isDiv = std::is_same_v<Op, std::divides<void>>;
        std::visit(
            [val]<typename U>(U & x) {
                if constexpr (isDiv and not std::is_same_v<U, Real>) {
                    // UB
                    assert(false);
                } else {
                    AssignOp{}(x, val);
                }
            },
            *this);

        return static_cast<T &>(*this);
    }

    template<typename T = StrictNumber>
    T ceilTp() const {
        return std::visit([](auto & x) -> T { return x.ceil(); }, *this);
    }
    template<typename T = StrictNumber>
    T floorTp() const {
        return std::visit([](auto & x) -> T { return x.floor(); }, *this);
    }

    template<typename T = StrictNumber>
    T & negateTp() {
        std::visit([](auto & x) { x.negate(); }, *this);
        return static_cast<T &>(*this);
    }
    template<typename T = StrictNumber>
    T & resetTp() noexcept {
        std::visit([](auto & x) { x.reset(); }, *this);
        return static_cast<T &>(*this);
    }

    static std::optional<Integer> tryMakeInteger(Real const & x) {
        if (not x.isIntegerValue()) { return std::nullopt; }
        return static_cast<Integer const &>(x);
    }
    bool tryTurnToInteger(Real & x) {
        if (not x.isIntegerValue()) { return false; }
        emplace<Integer>(std::move(x));
        return true;
    }
};

auto operator==(StrictNumber::variant const &, StrictNumber::variant const &) = delete;
auto operator!=(StrictNumber::variant const &, StrictNumber::variant const &) = delete;
auto operator<(StrictNumber::variant const &, StrictNumber::variant const &) = delete;
auto operator>(StrictNumber::variant const &, StrictNumber::variant const &) = delete;
auto operator<=(StrictNumber::variant const &, StrictNumber::variant const &) = delete;
auto operator>=(StrictNumber::variant const &, StrictNumber::variant const &) = delete;
auto operator<=>(StrictNumber::variant const &, StrictNumber::variant const &) = delete;

static_assert(std::constructible_from<StrictNumber, Integer>);
static_assert(std::constructible_from<StrictNumber, Real>);
static_assert(not std::convertible_to<StrictNumber, Integer>);
static_assert(not std::convertible_to<StrictNumber, Real>);

class FlexibleNumber : public StrictNumber {
public:
    using StrictNumber::StrictNumber;
    FlexibleNumber(std::integral auto val) : FlexibleNumber(Integer{val}) {}
    explicit FlexibleNumber(std::integral auto den, std::integral auto num) : FlexibleNumber({Real{den, num}}) {}
    explicit FlexibleNumber(char const *);

    operator Real() const { return makeReal(); }

    bool operator==(FlexibleNumber const & rhs) const { return std::is_eq(operator<=>(rhs)); }
    std::strong_ordering operator<=>(FlexibleNumber const & rhs) const { return compareTp(rhs); }

    FlexibleNumber operator+(FlexibleNumber const & rhs) const { return arithOperatorTp<std::plus<void>>(rhs); }
    FlexibleNumber operator-(FlexibleNumber const & rhs) const { return arithOperatorTp<std::minus<void>>(rhs); }
    FlexibleNumber operator*(FlexibleNumber const & rhs) const { return arithOperatorTp<std::multiplies<void>>(rhs); }
    FlexibleNumber operator/(FlexibleNumber const & rhs) const { return arithOperatorTp<std::divides<void>>(rhs); }
    FlexibleNumber & operator+=(FlexibleNumber const & rhs) { return arithAssignOperatorTp<std::plus<void>>(rhs); }
    FlexibleNumber & operator-=(FlexibleNumber const & rhs) { return arithAssignOperatorTp<std::minus<void>>(rhs); }
    FlexibleNumber & operator*=(FlexibleNumber const & rhs) {
        return arithAssignOperatorTp<std::multiplies<void>>(rhs);
    }
    FlexibleNumber & operator/=(FlexibleNumber const & rhs) { return arithAssignOperatorTp<std::divides<void>>(rhs); }
    FlexibleNumber operator+(std::integral auto val) const {
        return arithOperatorTp<std::plus<void>, FlexibleNumber>(val);
    }
    FlexibleNumber operator-(std::integral auto val) const {
        return arithOperatorTp<std::minus<void>, FlexibleNumber>(val);
    }
    FlexibleNumber operator*(std::integral auto val) const {
        return arithOperatorTp<std::multiplies<void>, FlexibleNumber>(val);
    }
    FlexibleNumber operator/(std::integral auto val) const {
        return arithOperatorTp<std::divides<void>, FlexibleNumber>(val);
    }
    FlexibleNumber & operator+=(std::integral auto val) {
        return arithAssignOperatorTp<std::plus<void>, FlexibleNumber>(val);
    }
    FlexibleNumber & operator-=(std::integral auto val) {
        return arithAssignOperatorTp<std::minus<void>, FlexibleNumber>(val);
    }
    FlexibleNumber & operator*=(std::integral auto val) {
        return arithAssignOperatorTp<std::multiplies<void>, FlexibleNumber>(val);
    }
    FlexibleNumber & operator/=(std::integral auto val) {
        return arithAssignOperatorTp<std::divides<void>, FlexibleNumber>(val);
    }

    FlexibleNumber ceil() const { return ceilTp<FlexibleNumber>(); }
    FlexibleNumber floor() const { return floorTp<FlexibleNumber>(); }

    FlexibleNumber & negate() { return negateTp<FlexibleNumber>(); }
    FlexibleNumber & reset() noexcept { return resetTp<FlexibleNumber>(); }
};

static_assert(std::constructible_from<FlexibleNumber, Integer>);
static_assert(std::constructible_from<FlexibleNumber, Real>);
static_assert(not std::convertible_to<FlexibleNumber, Integer>);
static_assert(std::convertible_to<FlexibleNumber, Real>);

static_assert(std::derived_from<FlexibleNumber, StrictNumber>);

// This way it works both for StrictNumber and FlexibleNumber
constexpr StrictNumber const & castStrict(StrictNumber const & n) {
    return static_cast<StrictNumber const &>(n);
}
constexpr StrictNumber & castStrict(StrictNumber & n) {
    return static_cast<StrictNumber &>(n);
}
constexpr StrictNumber && castStrict(StrictNumber && n) {
    return static_cast<StrictNumber &&>(n);
}

constexpr FlexibleNumber const & castFlexible(StrictNumber const & n) {
    return static_cast<FlexibleNumber const &>(n);
}
constexpr FlexibleNumber & castFlexible(StrictNumber & n) {
    return static_cast<FlexibleNumber &>(n);
}
constexpr FlexibleNumber && castFlexible(StrictNumber && n) {
    return static_cast<FlexibleNumber &&>(n);
}

inline Integer const & castInteger(StrictNumber const & n) {
    assert(n.isInteger());
    return *n.tryGetInteger();
}
inline Integer & castInteger(StrictNumber & n) {
    return const_cast<Integer &>(castInteger(std::as_const(n)));
}

inline Real const & castReal(StrictNumber const & n) {
    assert(n.isReal());
    return *n.tryGetReal();
}
inline Real & castReal(StrictNumber & n) {
    return const_cast<Real &>(castReal(std::as_const(n)));
}

// To have more control over the code, we use the stricter variant by default
// If flexibility is desired, explicitly use `castFlexible`
using Number = StrictNumber;

static_assert(number<Integer>);
static_assert(number<Real>);
static_assert(number<StrictNumber>);
static_assert(number<FlexibleNumber>);
static_assert(number<Number>);

template<typename T = Number>
inline T makeNumber(Integer x, bool makeReal = false) {
    T n{std::move(x)};
    assert(n.isInteger());
    if (makeReal) { n.turnToReal(); }
    return n;
}
template<typename T = Number>
inline T makeNumber(Real x, bool makeInt = false) {
    constexpr bool const isStrict = std::is_same_v<T, StrictNumber>;
    T n{std::move(x)};
    assert(n.isReal());
    if (makeInt) {
        [[maybe_unused]] bool const success = n.tryTurnToInteger();
        assert(not isStrict or success);
    }
    return n;
}
} // namespace opensmt

namespace std {
template<>
struct hash<opensmt::StrictNumber> : opensmt::StrictNumber::Hash {};
} // namespace std

#endif // OPENSMT_NUMBER_H
