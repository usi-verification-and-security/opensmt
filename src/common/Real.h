//
// Created by Martin Blicha on 18.02.18.
//

#ifndef OPENSMT_REAL_H
#define OPENSMT_REAL_H

#define FAST_RATIONALS

#ifdef FAST_RATIONALS
#include "FastRational.h"
#else
#include <gmpxx.h>
#endif

namespace opensmt {
#ifdef FAST_RATIONALS
using Real = FastRational;
using RealHash = FastRationalHash;
#else
using Real = mpq_class;
#endif
} // namespace opensmt

#endif // OPENSMT_REAL_H
