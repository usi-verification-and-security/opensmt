//
// Created by Martin Blicha on 18.02.18.
//

#ifndef OPENSMT_REAL_H
#define OPENSMT_REAL_H

/*#define FAST_RATIONALS 1

#ifdef FAST_RATIONALS

#include "FastRational.h"
#else
#include <gmpxx.h>
#endif

namespace opensmt {
#ifdef FAST_RATIONALS
    typedef FastRational Real;
#else
    typedef mpq_class Real;
#endif
}
*/


#include "Number.h"

namespace opensmt {
    typedef Number Real;
}

#endif //OPENSMT_REAL_H

