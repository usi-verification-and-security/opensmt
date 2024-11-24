//
// Created by Tomas Kolarik in 08/2024.
//

#ifndef OPENSMT_FAST_INTEGER_H
#define OPENSMT_FAST_INTEGER_H

#include "FastRational.h"

#include <concepts>

namespace opensmt {
// TODO: inefficient, rational representation & uses mpq instead of mpz
class FastInteger : public FastRational {
public:
    using FastRational::FastRational;
    explicit FastInteger(FastRational rat) : FastRational(std::move(rat)) { assert(isIntegerValue()); }
    explicit FastInteger(char const *, int const base = 10);
    FastInteger & operator=(FastRational const & other) {
        assert(this != &other);
        assert(other.isIntegerValue());
        FastRational::operator=(other);
        return *this;
    }
    FastInteger & operator=(FastRational && other) {
        assert(other.isIntegerValue());
        FastRational::operator=(std::move(other));
        return *this;
    }
    FastInteger & operator=(std::integral auto i) { return operator=(FastInteger(i)); }

    FastInteger ceil() const noexcept { return *this; }
    FastInteger floor() const noexcept { return *this; }

    FastInteger operator-() const { return static_cast<FastInteger &&>(FastRational::operator-()); }
    FastInteger operator+(FastInteger const & b) const {
        return static_cast<FastInteger &&>(FastRational::operator+(b));
    }
    FastInteger operator-(FastInteger const & b) const {
        return static_cast<FastInteger &&>(FastRational::operator-(b));
    }
    FastInteger operator*(FastInteger const & b) const {
        return static_cast<FastInteger &&>(FastRational::operator*(b));
    }
    FastInteger & operator+=(FastInteger const & b) {
        FastRational::operator+=(b);
        return *this;
    }
    FastInteger & operator-=(FastInteger const & b) {
        FastRational::operator-=(b);
        return *this;
    }
    FastInteger & operator*=(FastInteger const & b) {
        FastRational::operator*=(b);
        return *this;
    }
    FastInteger & operator+=(std::integral auto i) { return operator+=(FastInteger(i)); }
    FastInteger & operator-=(std::integral auto i) { return operator-=(FastInteger(i)); }
    FastInteger & operator*=(std::integral auto i) { return operator*=(FastInteger(i)); }
    FastRational & operator+=(FastRational const &) = delete;
    FastRational & operator-=(FastRational const &) = delete;
    FastRational & operator*=(FastRational const &) = delete;

    FastRational operator/(FastInteger const & b) const { return FastRational::operator/(b); }
    void operator/=(FastInteger const &) = delete;
    FastRational & operator/=(FastRational const &) = delete;

    // The return value will have the sign of d
    FastInteger operator%(FastInteger const & d) const {
        assert(isIntegerValue() && d.isIntegerValue());
        if (wordPartValid() && d.wordPartValid()) {
            uword w = absVal(num % d.num);     // Largest value is absVal(INT_MAX % INT_MIN) = INT_MAX
            return (word)(d.num > 0 ? w : -w); // No overflow since 0 <= w <= INT_MAX
        }
        FastRational r = operator/(d);
        auto i = FastInteger(r.floor());
        return operator-(i * d);
    }
    FastInteger & operator%=(FastInteger const & d) {
        //+ it would be more efficient the other way around
        return operator=(operator%(d));
    }

    std::optional<word> tryGetValue() const {
        if (!wordPartValid()) return {};
        return num;
    }

private:
    FastInteger(std::integral auto, std::integral auto) = delete;

    using FastRational::get_d;
    using FastRational::get_den;
    using FastRational::get_num;
    using FastRational::tryGetNumDen;

    friend FastInteger gcd(FastInteger const &, FastInteger const &);
    friend FastInteger lcm(FastInteger const &, FastInteger const &);
    friend FastInteger fastint_fdiv_q(FastInteger const &, FastInteger const &);
    friend FastInteger divexact(FastInteger const &, FastInteger const &);
};

static_assert(!std::integral<FastInteger>);

// The result could not fit into integer -> FastInteger
template<std::integral integer>
FastInteger lcm(integer a, integer b) {
    if (a == 0) return 0;
    if (b == 0) return 0;
    FastRational rat = (b > a) ? FastRational(b / gcd(a, b)) * a : FastRational(a / gcd(a, b)) * b;
    assert(rat.isIntegerValue());
    return static_cast<FastInteger&&>(rat);
}

FastInteger gcd(FastInteger const &, FastInteger const &);
FastInteger lcm(FastInteger const &, FastInteger const &);
FastInteger fastint_fdiv_q(FastInteger const & n, FastInteger const & d);
FastInteger divexact(FastInteger const & n, FastInteger const & d);
} // namespace opensmt

#endif // OPENSMT_FAST_INTEGER_H
