/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2017 Antti Hyvarinen

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


#ifndef BVSTORE_H
#define BVSTORE_H

#include "Bvector.h"

class BVStore
{
    BvectorAllocator bva;
    vec<BVRef>  idToBVRef;
    Map<PTRef,BVRef,PTRefHash> bv_map;  // Mapping of a BV variable to the bit vector (automatic)
    Map<PTRef,PTRef,PTRefHash> carryonly; // A cache mapping sum PTRefs to their carry bit
    vec<PTRef> bitVectorTerms;

public:
    BVStore();
    BVRef newBvector(vec<PTRef> const & asgn, PTRef act_var, PTRef tr) {
        BVRef br = bva.alloc(asgn, act_var); idToBVRef.push(br);
        bv_map.insert(tr, br);
        bitVectorTerms.push(tr);
        return br;
    }

    BVRef newBvector(vec<PTRef> const & asgn, PTRef tr) {
        return newBvector(asgn, PTRef_Undef, tr);
    }

    void free(BVRef r) { bva.free(r); }
    Bvector& operator[] (BVRef br) { return bva[br]; }
    const Bvector& operator[] (BVRef br) const { return bva[br]; }
    BVRef operator[] (PTRef tr) { if (!has(tr)) return BVRef_Undef; return getFromPTRef(tr); }

    bool  has(PTRef r) { return bv_map.has(r); }
    bool  has_carryonly(PTRef tr) { return carryonly.has(tr); }
    PTRef getCarryOnly(PTRef tr)  { return carryonly[tr]; }
    void  insertCarryOnly(PTRef tr_sum, PTRef tr_carry) { carryonly.insert(tr_sum, tr_carry); }
    BVRef getFromPTRef(PTRef r) const { assert(bv_map.has(r)); return bv_map[r]; }
    void  copyAsgnTo(BVRef bv, vec<PTRef>& tr_vec)  { for (int i = 0; i < operator[](bv).size(); i++) tr_vec.push(operator[](bv)[i]); }

    vec<PTRef> const & getBitVectorTerms() const { return bitVectorTerms; }
    int   size() const { return idToBVRef.size(); }
};

#endif
