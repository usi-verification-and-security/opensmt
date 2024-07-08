//
// Created by Martin Blicha on 18.02.18.
//

#ifndef OPENSMT_NUMBER_H
#define OPENSMT_NUMBER_H

#define FAST_RATIONALS 1

#ifdef FAST_RATIONALS
#include "FastRational.h"
#else
#include <gmpxx.h>
#endif

namespace opensmt {
#ifdef FAST_RATIONALS
    using Number = FastRational;
    using NumberHash = FastRationalHash;
#else
    using Number = mpq_class;
#endif
} // namespace opensmt

inline bool isNegative(opensmt::Number const & num) {
    return num.sign() < 0;
}

inline bool isPositive(opensmt::Number const & num) {
    return num.sign() > 0;
}

inline bool isNonNegative(opensmt::Number const & num) {
    return num.sign() >= 0;
}

inline bool isNonPositive(opensmt::Number const & num) {
    return num.sign() <= 0;
}

#endif // OPENSMT_NUMBER_H
