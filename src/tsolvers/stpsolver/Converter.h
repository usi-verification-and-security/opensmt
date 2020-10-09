#ifndef OPENSMT_CONVERTER_H
#define OPENSMT_CONVERTER_H

#include "FastRational.h"

template<class T>
class Converter {
public:
    // Converts a FastRational value to a T value
    static T getValue(const FastRational &val);
    // given (a-b<=c), returns c' such that not(a-b<=c) == (b-a<=c')
    static T negate(const T &val);
    // Converts given T to a string
    static std::string show(const T &val);

    Converter() = delete;
};

#endif //OPENSMT_CONVERTER_H
