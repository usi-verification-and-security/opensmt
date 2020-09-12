#ifndef OPENSMT_SAFEINT_HPP
#define OPENSMT_SAFEINT_HPP

#include <cstddef>
#include <stdexcept>

struct SafeInt {
private:
    ptrdiff_t val;
public:
    SafeInt() = default;
    SafeInt(ptrdiff_t val) : val(val) {}

    ptrdiff_t value() const { return val; }

    SafeInt operator +(SafeInt other) const {
        ptrdiff_t res;
        if (__builtin_saddl_overflow(val, other.val, &res)) {
            throw std::overflow_error("Overflow detected during SafeInt addition");
        }
        return SafeInt(res);
    }

    SafeInt & operator -=(SafeInt other) {
        ptrdiff_t res;
        if (__builtin_ssubl_overflow(val, other.val, &res)) {
            throw std::underflow_error("Underflow detected during SafeInt subtraction");
        }
        val = res;
        return *this;
    }

    bool operator ==(SafeInt other) const {
        return val == other.val;
    }

    bool operator >=(SafeInt other) const {
        return val >= other.val;
    }

    bool operator >(SafeInt other) const {
        return val > other.val;
    }

    bool operator <=(SafeInt other) const {
        return val <= other.val;
    }

    SafeInt operator -() const {
        return SafeInt(-val);
    }
};

#endif //OPENSMT_SAFEINT_HPP
