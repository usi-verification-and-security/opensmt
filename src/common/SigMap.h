#ifndef SIGPAIR_H
#define SIGPAIR_H

#include "minisat/mtl/Map.h"
#include "CgTypes.h"

//===================================================================================================
// Specializations for signature pair hashing (Map from mtl)
//

class SigPair {
public:
    cgId x;
    cgId y;
    SigPair(cgId id1, cgId id2) : x(id1), y(id2) {}
    SigPair() : x(cgId_Nil), y(cgId_Nil) {}
};

struct SigHash {
    uint32_t operator () (const SigPair& s) const { return s.x + s.y; } };

template <>
struct Equal<const SigPair&> {
    bool operator() (const SigPair& s1, const SigPair& s2) const {
        return (s1.x == s2.x) && (s1.y == s2.y); };
};
#endif
