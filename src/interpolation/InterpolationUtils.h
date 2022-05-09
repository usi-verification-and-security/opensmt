/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */
#ifndef OPENSMT_INTERPOLATIONUTILS_H
#define OPENSMT_INTERPOLATIONUTILS_H

#include <gmpxx.h>

#include "OpensmtAssert.h"
#include <set>

namespace opensmt {
enum class icolor_t : char {
    I_UNDEF = 0,
    I_A = 1,
    I_B = 2,
    I_AB = I_A | I_B,
    I_S = 4
};

inline constexpr icolor_t operator| (icolor_t f, icolor_t s) {
    return static_cast<icolor_t>(static_cast<std::underlying_type_t<icolor_t>>(f) | static_cast<std::underlying_type_t<icolor_t>>(s));
}

inline constexpr icolor_t operator& (icolor_t f, icolor_t s) {
    return static_cast<icolor_t>(static_cast<std::underlying_type_t<icolor_t>>(f) & static_cast<std::underlying_type_t<icolor_t>>(s));
}

inline std::string colorToString(icolor_t c) {
    switch (c) {
        case icolor_t::I_UNDEF: return "UNDEF";
        case icolor_t::I_A: return "A";
        case icolor_t::I_B: return "B";
        case icolor_t::I_AB: return "AB";
        case icolor_t::I_S: return "S";
        default:
            assert(false);
            throw std::logic_error("Unreachable");
    }
}

using ipartitions_t = mpz_class;

inline void setbit(ipartitions_t & p, const unsigned b) { mpz_setbit(p.get_mpz_t(), b); }

inline void clrbit(ipartitions_t & p, const unsigned b) { mpz_clrbit(p.get_mpz_t(), b); }

inline int tstbit(const ipartitions_t & p, const unsigned b) { return mpz_tstbit(p.get_mpz_t(), b); }

// Set rop to op1 bitwise-and op2.
inline void andbit(ipartitions_t & ipres, const ipartitions_t & ip1, const ipartitions_t & ip2) {
    mpz_and(ipres.get_mpz_t(), ip1.get_mpz_t(), ip2.get_mpz_t());
}

// Set rop to op1 bitwise inclusive-or op2.
inline void orbit(ipartitions_t & ipres, const ipartitions_t & ip1, const ipartitions_t & ip2) {
    mpz_ior(ipres.get_mpz_t(), ip1.get_mpz_t(), ip2.get_mpz_t());
}

inline bool isAlocal (const ipartitions_t & p, const ipartitions_t & mask) { return (p & mask) != 0; }
inline bool isBlocal (const ipartitions_t & p, const ipartitions_t & mask) { return (p & ~mask) != 0; }
inline bool isAstrict(const ipartitions_t & p, const ipartitions_t & mask) { return isAlocal(p, mask) and not isBlocal(p, mask); }
inline bool isBstrict(const ipartitions_t & p, const ipartitions_t & mask) { return isBlocal( p, mask ) and not isAlocal(p, mask); }
inline bool isAB     (const ipartitions_t & p, const ipartitions_t & mask) { return isAlocal( p, mask ) and isBlocal(p, mask); }

// To specify the tree structure of a collection of partitions
// NOTE Partitions should be tagged with consecutive ids >=1
class InterpolationTree
{
public:
    InterpolationTree(int _partition_id):
            partition_id(_partition_id),
            parent(NULL)
    {}

    void addChild (InterpolationTree* _tree){
        children.insert(_tree);
        (*_tree).setParent(this);
    }

    void setParent(InterpolationTree* _parent){
        parent = _parent;
    }

    int getPartitionId() { return partition_id; }
    std::set<InterpolationTree*>& getChildren() { return children; }
    InterpolationTree* getParent() {return parent; }

private:
    // NOTE if the tree has N nodes, the partition ids go from 1 to N
    int partition_id;                         // The integer corresponding to the partition id
    std::set<InterpolationTree*>  children;        // The children of the node in the tree
    InterpolationTree* parent;
};
}

// TODO: Remove these using from header file
using opensmt::ipartitions_t;
using opensmt::icolor_t;

#endif //OPENSMT_INTERPOLATIONUTILS_H
