//
// Created by Martin Blicha on 18.02.18.
//

#ifndef OPENSMT_REAL_H
#define OPENSMT_REAL_H

//- #define FAST_RATIONALS
#define FLOATS

#ifdef FAST_RATIONALS
#include "FastRational.h"
#elif defined(FLOATS)
#include "Float.h"
#else
#include <gmpxx.h>
#endif

namespace opensmt {
#ifdef FAST_RATIONALS
using Real = FastRational;
using RealHash = FastRationalHash;
#elif defined(FLOATS)
using Real = Float;
using RealHash = Float::Hash;
#else
using Real = mpq_class;
#endif
} // namespace opensmt

#endif // OPENSMT_REAL_H
