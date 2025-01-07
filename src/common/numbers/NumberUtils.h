/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_NUMBERUTILS_H
#define OPENSMT_NUMBERUTILS_H

#include <cassert>

#include <gmp.h>
#include <gmpxx.h>

namespace opensmt {
    typedef mpz_class Integer; //PS. related to BV logic

    void static inline wordToBinary(const Integer x, char *&bin, const int width) {
        bin = (char *) malloc(width + 1);

        int p = 0;
        Integer one = 1;
        for (Integer i = (one << (width - 1)); i > 0; i >>= 1)
            bin[p++] = ((x & i) == i) ? '1' : '0';
        bin[p] = '\0';
    }

    void static inline wordToBinary(const unsigned x, char *&bin, const int width) {
        bin = (char *) malloc(width + 1);

        int p = 0;
        Integer one = 1;
        for (Integer i = (one << (width - 1)); i > 0; i >>= 1)
            bin[p++] = ((x & i) == i) ? '1' : '0';
        bin[p] = '\0';
    }

    void static inline normalize(char *&rat, const char *flo, bool is_neg) {
        mpq_t num;
        mpq_init(num);
        int val = mpq_set_str(num, flo, 0);
        (void) val;
        assert(val != -1);
        mpq_canonicalize(num);
        if (is_neg)
            mpq_neg(num, num);
        gmp_asprintf(&rat, "%Qd", num);
        mpq_clear(num);
    }

    static inline bool isPowOfTwo(int b) {
        return b && !(b & (b - 1));
    }

    static inline int getLogFromPowOfTwo(int l) {
        assert(isPowOfTwo(l));
        if (l == 1) return 0;
        int n = 0;
        while ((2 << (n++)) != l);
        return n;
    }
}
#endif //OPENSMT_NUMBERUTILS_H
