/*
 * Copyright (c) 2012-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_PTHELPERSTRUCTS_H
#define OPENSMT_PTHELPERSTRUCTS_H

#include "SolverTypes.h"
#include "PTRef.h"

class PtAsgn {
public:
    PTRef tr;
    lbool sgn;
    PtAsgn(PTRef tr_, lbool sgn_) : tr(tr_), sgn(sgn_) {}
    PtAsgn() : tr(PTRef_Undef), sgn(l_Undef) {}
    bool operator== (PtAsgn const & other) const { return tr == other.tr and sgn == other.sgn; }
    bool operator!= (PtAsgn const & other) const { return not (*this == other); }
    bool operator> (PtAsgn const & other) const { return tr > other.tr or (tr == other.tr and toInt(sgn) > toInt(other.sgn)); }
    bool operator< (PtAsgn const & other) const { return tr < other.tr or (tr == other.tr and toInt(sgn) < toInt(other.sgn)); }
};

// Strict weak ordering of PtAsgn: Instances with same tr, but different sgn are treated as equivalent.
// OK to be used in sorting, see https://en.cppreference.com/w/cpp/named_req/Compare
struct LessThan_PtAsgn {
    bool operator() (PtAsgn x, PtAsgn y) {
        return x.tr.x < y.tr.x;
    }
};

static class PtAsgn PtAsgn_Undef(PTRef_Undef, l_Undef);

struct PtAsgnHash {
    uint32_t operator () (const PtAsgn& s) const;/* {
        return ((uint32_t)s.tr.x << 2) + toInt(s.sgn);
    }*/
};

class PtAsgn_reason {
public:
    PTRef tr;
    PTRef reason;
    lbool sgn;
    PtAsgn_reason(PTRef tr_, lbool sgn_, PTRef reason_)
            : tr(tr_)
            , reason(reason_)
            , sgn(sgn_)
    {}
    PtAsgn_reason() : tr(PTRef_Undef), reason(PTRef_Undef), sgn(l_Undef) {}
};

static class PtAsgn_reason PtAsgn_reason_Undef(PTRef_Undef, l_Undef, PTRef_Undef);

#endif //OPENSMT_PTHELPERSTRUCTS_H
