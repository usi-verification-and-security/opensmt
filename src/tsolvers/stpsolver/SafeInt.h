#ifndef OPENSMT_SAFEINT_H
#define OPENSMT_SAFEINT_H

#include <cstddef>
#include <stdexcept>

struct SafeInt {
private:
    ptrdiff_t val;
public:
    SafeInt() = default;

    explicit SafeInt(ptrdiff_t val) : val(val) {}

    ptrdiff_t value() const { return val; }

    SafeInt operator+(SafeInt other) const {
        // a+b > MAX ==> MAX-a < b                     // a+b < MIN ==> MIN-a > b
        if ((val > 0 && PTRDIFF_MAX - val < other.val) || (val < 0 && PTRDIFF_MIN - val > other.val)) {
            throw std::overflow_error("Overflow detected during SafeInt addition");
        }
        return SafeInt(val + other.val);
    }

    SafeInt &operator-=(SafeInt other) {
        if ((other.val > 0 && PTRDIFF_MIN + other.val > val) || (other.val < 0 && PTRDIFF_MAX + other.val < val)) {
            throw std::underflow_error("Underflow detected during SafeInt subtraction");
        }
        val -= other.val;
        return *this;
    }

    bool operator==(SafeInt other) const { return val == other.val; }

    bool operator>=(SafeInt other) const { return val >= other.val; }

    bool operator>(SafeInt other) const { return val > other.val; }

    bool operator<=(SafeInt other) const { return val <= other.val; }

    SafeInt operator-(SafeInt other) const {
        SafeInt res = *this;
        res -= other;
        return res;
    }

    SafeInt operator-() const { return SafeInt(-val); }
};

#endif //OPENSMT_SAFEINT_H
