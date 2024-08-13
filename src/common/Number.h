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

inline bool isNegative(Number const & num) {
    return num.sign() < 0;
}

inline bool isPositive(Number const & num) {
    return num.sign() > 0;
}

inline bool isNonNegative(Number const & num) {
    return num.sign() >= 0;
}

inline bool isNonPositive(Number const & num) {
    return num.sign() <= 0;
}
} // namespace opensmt

#endif // OPENSMT_NUMBER_H
