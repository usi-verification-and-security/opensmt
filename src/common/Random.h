//
// Created by Antti Hyvarinen on 07.05.22.
//

#ifndef OPENSMT_RANDOM_H
#define OPENSMT_RANDOM_H

namespace opensmt {
    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double &seed) {
        assert(seed != 0);
        seed *= 1389796;
        int q = (int) (seed / 2147483647);
        seed -= (double) q * 2147483647;
        return seed / 2147483647;
    }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double &seed, int size) {
        return (int) (drand(seed) * size);
    }
}
#endif //OPENSMT_RANDOM_H
