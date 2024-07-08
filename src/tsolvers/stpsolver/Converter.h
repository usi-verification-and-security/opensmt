#ifndef OPENSMT_CONVERTER_H
#define OPENSMT_CONVERTER_H

#include "Number.h"
#include <concepts>
#include <cstddef>

template<class T>
class Converter {
public:
    // Converts a given value to a T value
    static T getValue(opensmt::Number const & val);
    static T getValue(ptrdiff_t val);
    static T getValue(std::signed_integral auto val) { return getValue(static_cast<ptrdiff_t>(val)); }

    // given (a-b<=c), returns c' such that not(a-b<=c) == (b-a<=c')
    static T negate(T const & val);

    // Converts given T to a string
    static std::string show(T const & val);

    Converter() = delete;
};

#endif // OPENSMT_CONVERTER_H
