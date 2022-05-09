//
// Created by usi on 09.05.22.
//

#ifndef OPENSMT_OPENSMTASSERT_H
#define OPENSMT_OPENSMTASSERT_H

#ifdef OSMT_ASSERT_THROWS
#include "OsmtAssertException.h"

#ifdef assert
#undef assert
#endif // assert

#define	assert(e) \
    do { if (!(e)) { throw OsmtAssertException(__FILE__, __LINE__, "assertion failed"); } } while (0)
#else
#include <cassert>
#endif

#endif //OPENSMT_OPENSMTASSERT_H
