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
        return val + other.val;
    }

    SafeInt & operator -=(SafeInt other) {
        val -= other.val;
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
        return {-val};
    }
};

#endif //OPENSMT_SAFEINT_HPP
