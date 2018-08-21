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
    typedef FastRational Number;
#else
    typedef mpq_class Number;
#endif
}

#endif //OPENSMT_NUMBER_H
