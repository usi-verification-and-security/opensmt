/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifndef OPENSMT_PTHELPERSTRUCTS_H
#define OPENSMT_PTHELPERSTRUCTS_H

#include <string.h>
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

struct LessThan_PtAsgn {
    bool operator () (PtAsgn x, PtAsgn y) {
        return x.tr.x < y.tr.x;
    }
};

// DEPRECATED in favour of new Model structure, should not be used anymore!
class ValPair
{
public:
    PTRef tr;
    char* val;
    ValPair() : tr(PTRef_Undef), val(nullptr) {}
    ~ValPair();/* {
        if (val != NULL)
            free(val);
    }*/
    ValPair(PTRef tr, const char* val_) : tr(tr) {
        if (val_ != NULL)
            val = strdup(val_);
        else val = NULL;
    }
    ValPair(const ValPair& other);/* {
        tr = other.tr;
        if (other.val != NULL)
            val = strdup(other.val);
        else val = NULL;
    }*/
    const ValPair& operator= (const ValPair& other);/* {
        tr = other.tr;
        if (other.val != NULL)
            val = strdup(other.val);
        else val = NULL;
        return *this;
    }*/
    bool operator== (const ValPair& other) const;// { return tr == other.tr && val == other.val; }
    bool operator!= (const ValPair& other) const;// { return tr != other.tr || val != other.val; }
};

static class ValPair ValPair_Undef(PTRef_Undef, nullptr);

#endif //OPENSMT_PTHELPERSTRUCTS_H
