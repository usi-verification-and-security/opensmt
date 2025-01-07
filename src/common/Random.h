/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_RANDOM_H
#define OPENSMT_RANDOM_H

#include <cassert>

namespace opensmt {
// Returns a random float 0 <= x < 1. Seed must never be 0.
static inline double drand(double & seed) {
    assert(seed != 0);
    seed *= 1389796;
    int q = (int)(seed / 2147483647);
    seed -= (double)q * 2147483647;
    return seed / 2147483647;
}

// Returns a random integer 0 <= x < size. Seed must never be 0.
static inline int irand(double & seed, int size) {
    return (int)(drand(seed) * size);
}
} // namespace opensmt

#endif // OPENSMT_RANDOM_H
