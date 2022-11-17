/*
 * Copyright (c) 2012-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_PTREF_H
#define OPENSMT_PTREF_H

#include <cstdint>
#include <functional>

struct PTRef {
    uint32_t x;
    inline friend bool operator== (PTRef a1, PTRef a2) { return a1.x == a2.x; }
    inline friend bool operator!= (PTRef a1, PTRef a2) { return a1.x != a2.x; }
    inline friend bool operator> (PTRef a1, PTRef a2) { return a1.x > a2.x; }
    inline friend bool operator< (PTRef a1, PTRef a2) { return a1.x < a2.x; }
    static const PTRef Undef;
};

const struct PTRef PTRef_Undef = {INT32_MAX};
inline constexpr PTRef PTRef::Undef = PTRef { INT32_MAX };

struct PTRefHash {
    uint32_t operator () (PTRef s) const {
        return (uint32_t)s.x; }
};

struct PTRefPairHash {
    std::size_t operator () (std::pair<PTRef, PTRef> p) const {
        std::hash<uint32_t> hasher;
        return (hasher(p.first.x) ^ hasher(p.second.x));
    }
};

#endif //OPENSMT_PTREF_H
