//
// Created by Tomas Kolarik on 06.11.24
//

#ifndef OPENSMT_NUMBERCONCEPT_H
#define OPENSMT_NUMBERCONCEPT_H

#include <concepts>
#include <iosfwd>
#include <string>

namespace opensmt {
template<typename T>
concept number = requires(T & t, std::ostream & os) {
    { t.sign() } -> std::convertible_to<bool>;
    { t.isZero() } -> std::convertible_to<bool>;
    { t.isOne() } -> std::convertible_to<bool>;
    { t.isIntegerValue() } -> std::convertible_to<bool>;
    { t.ceil() } -> std::same_as<T>;
    { t.floor() } -> std::same_as<T>;
    t.negate();
    t.reset();
    { t.toString() } -> std::convertible_to<std::string>;
    t.print(os);
    { t.hash() } -> std::convertible_to<std::size_t>;
};

inline bool isNegative(number auto const & x) {
    return x.sign() < 0;
}

inline bool isPositive(number auto const & x) {
    return x.sign() > 0;
}

inline bool isNonNegative(number auto const & x) {
    return x.sign() >= 0;
}

inline bool isNonPositive(number auto const & x) {
    return x.sign() <= 0;
}

template<number T>
inline T operator-(T x) {
    x.negate();
    return x;
}

template<number T>
inline T abs(T const & x) {
    if (isNonNegative(x)) {
        return x;
    } else {
        return -x;
    }
}

inline std::ostream & operator<<(std::ostream & os, number auto const & x) {
    x.print(os);
    return os;
}
} // namespace opensmt

#endif // OPENSMT_NUMBERCONCEPT_H
