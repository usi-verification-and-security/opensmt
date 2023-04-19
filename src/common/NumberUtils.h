/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_NUMBERUTILS_H
#define OPENSMT_NUMBERUTILS_H

#include <gmp.h>
#include <gmpxx.h>

namespace opensmt {
    typedef mpz_class Integer; //PS. related to BV logic

    template<typename I>
    static inline std::string wordToBinary(I const & x, int width) {
        std::string bin;
        bin.resize(width);
        int p = 0;
        I one = 1;
        for (opensmt::Integer i = (one << (width - 1)); i > 0; i >>= 1)
            bin[p++] = ((x & i) == i) ? '1' : '0';
        return bin;
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

    static inline bool isNumber(std::string const & n) { return not n.empty() and std::for_each(n.begin(), n.end(), [](char c) { return std::isdigit(c); }); }
}
#endif //OPENSMT_NUMBERUTILS_H
