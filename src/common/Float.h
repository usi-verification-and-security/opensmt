#ifndef OPENSMT_FLOAT_H
#define OPENSMT_FLOAT_H

//- !!!
#include "FastInteger.h"

#include <string>
#include <concepts>
#include <cassert>
#include <cmath>

namespace opensmt {
    class Float {
    public:
        struct Hash;

        using Value = double;

        static_assert(std::floating_point<Value>);

        Float() = default;
        ~Float() = default;
        Float(Float const &) = default;
        Float(Float &&) = default;
        Float & operator =(Float const &) = default;
        Float & operator =(Float &&) = default;

        constexpr Float(Value) noexcept;
        constexpr Float(std::floating_point auto val) : Float(Value(val)) { }
        constexpr Float(std::integral auto val) : Float(Value(val)) { }
        //- !!!
        explicit Float(FastInteger const & fastint) : Float(static_cast<FastRational const &>(fastint).tryGetNumDen()->first) { }
        //- !!!
        explicit Float(FastRational const & fastrat) : Float(fastrat.tryGetNumDen()->first, fastrat.tryGetNumDen()->second) { }
        explicit constexpr Float(std::integral auto den, std::integral auto num);
        explicit Float(char const *);

        Value value() const noexcept { return _value; }
        Value & value() noexcept { return _value; }

        int sign() const {
            auto const val = value();
            if (val > 0) return 1;
            if (val < 0) return -1;
            return 0;
        }

        bool isZero() const { return value() == 0; }
        bool isOne() const { return value() == 1; }

        bool isInteger() const {
            auto const val = value();
            return val == std::trunc(val);
        }

        bool operator ==(Float const & other) const { return value() == other.value(); }
        bool operator !=(Float const & other) const { return value() != other.value(); }
        bool operator < (Float const & other) const { return value() <  other.value(); }
        bool operator > (Float const & other) const { return value() >  other.value(); }
        bool operator <=(Float const & other) const { return value() <= other.value(); }
        bool operator >=(Float const & other) const { return value() >= other.value(); }

        int compare(Float const & other) const {
            if (*this > other) return 1;
            if (*this < other) return -1;
            return 0;
        }

        Float operator -() const { return -value(); }
        Float operator +() const { return value(); }
        Float operator +(Float const & other) const { return value() + other.value(); }
        Float operator -(Float const & other) const { return value() - other.value(); }
        Float operator *(Float const & other) const { return value() * other.value(); }
        Float operator /(Float const & other) const { return value() / other.value(); }
        Float & operator +=(Float const & other) { value() += other.value(); return *this; }
        Float & operator -=(Float const & other) { value() -= other.value(); return *this; }
        Float & operator *=(Float const & other) { value() *= other.value(); return *this; }
        Float & operator /=(Float const & other) { value() /= other.value(); return *this; }

        //- !!!
        Float operator +(FastInteger const & other) const { return operator+(Float(other)); }
        Float operator -(FastInteger const & other) const { return operator-(Float(other)); }
        Float operator *(FastInteger const & other) const { return operator*(Float(other)); }
        Float operator /(FastInteger const & other) const { return operator/(Float(other)); }
        Float & operator +=(FastInteger const & other) { return operator+=(Float(other)); }
        Float & operator -=(FastInteger const & other) { return operator-=(Float(other)); }
        Float & operator *=(FastInteger const & other) { return operator*=(Float(other)); }
        Float & operator /=(FastInteger const & other) { return operator/=(Float(other)); }

        //- !!!
        Float operator +(std::integral auto other) const { return operator+(Float(other)); }
        Float operator -(std::integral auto other) const { return operator-(Float(other)); }
        Float operator *(std::integral auto other) const { return operator*(Float(other)); }
        Float operator /(std::integral auto other) const { return operator/(Float(other)); }
        Float & operator +=(std::integral auto other) { return operator+=(Float(other)); }
        Float & operator -=(std::integral auto other) { return operator-=(Float(other)); }
        Float & operator *=(std::integral auto other) { return operator*=(Float(other)); }
        Float & operator /=(std::integral auto other) { return operator/=(Float(other)); }

        Float abs() const {
            return std::abs(value());
        }

        Float inverse() const {
            return 1./value();
        }

        Float ceil() const {
            return std::ceil(value());
        }

        Float floor() const {
            return std::floor(value());
        }

        void negate() & {
            if (isZero()) return;
            value() = -value();
            assert(normalized(value()));
        }

        void reset() & noexcept {
            value() = 0;
        }

        double get_d() const { return value(); }

        std::string get_str() const;
        void print(std::ostream &) const;
        friend std::ostream & operator <<(std::ostream & os, Float const & x) {
            x.print(os);
            return os;
        }
    protected:
        static constexpr bool normalized(Value) noexcept;
        static constexpr Value normalize(Value) noexcept;
    private:
        Value _value;
    };
}

namespace opensmt {
    struct Float::Hash {
        std::size_t operator ()(Float const & x) const noexcept {
            return std::hash<Float::Value>{}(x.value());
        }
    };

    constexpr Float::Float(Value val) noexcept : _value{normalize(val)} { }

    constexpr Float::Float(std::integral auto den, std::integral auto num) : Float(Value(den)/Value(num)) {
        assert(normalized(value()));
    }

    constexpr bool Float::normalized(Value val) noexcept {
        return !std::signbit(val) || val < 0;
    }

    constexpr Float::Value Float::normalize(Value val) noexcept {
        static_assert(0. == -0.);
        if (val == 0) {
            assert(normalized(0));
            return 0;
        }
        assert(normalized(val));
        return val;
    }

    inline Float abs(Float const & x) { return x.abs(); }

    inline int cmpabs(Float const & a, Float const & b) {
        return abs(a).compare(abs(b));
    };

    inline void addition      (Float & dst, Float const & a, Float const & b) { dst = a + b; }
    inline void subtraction   (Float & dst, Float const & a, Float const & b) { dst = a - b; }
    inline void multiplication(Float & dst, Float const & a, Float const & b) { dst = a * b; }
    inline void division      (Float & dst, Float const & a, Float const & b) { dst = a / b; }
    inline void additionAssign      (Float & a, Float const & b) { a += b; }
    inline void subtractionAssign   (Float & a, Float const & b) { a -= b; }
    inline void multiplicationAssign(Float & a, Float const & b) { a *= b; }
    inline void divisionAssign      (Float & a, Float const & b) { a /= b; }
}

namespace std {
    template <>
    struct hash<opensmt::Float> : opensmt::Float::Hash {};
}

#endif //OPENSMT_FLOAT_H
