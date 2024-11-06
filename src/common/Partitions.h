/*
 *  Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef PARTITIONS_H
#define PARTITIONS_H

#include <gmpxx.h>

namespace opensmt {

using ipartitions_t = mpz_class;

inline void setbit(ipartitions_t & p, unsigned const b) {
    mpz_setbit(p.get_mpz_t(), b);
}

inline void clrbit(ipartitions_t & p, unsigned const b) {
    mpz_clrbit(p.get_mpz_t(), b);
}

inline int tstbit(ipartitions_t const & p, unsigned const b) {
    return mpz_tstbit(p.get_mpz_t(), b);
}

// Set rop to op1 bitwise-and op2.
inline void andbit(ipartitions_t & ipres, ipartitions_t const & ip1, ipartitions_t const & ip2) {
    mpz_and(ipres.get_mpz_t(), ip1.get_mpz_t(), ip2.get_mpz_t());
}

// Set rop to op1 bitwise inclusive-or op2.
inline void orbit(ipartitions_t & ipres, ipartitions_t const & ip1, ipartitions_t const & ip2) {
    mpz_ior(ipres.get_mpz_t(), ip1.get_mpz_t(), ip2.get_mpz_t());
}

} // namespace opensmt

#endif // PARTITIONS_H
