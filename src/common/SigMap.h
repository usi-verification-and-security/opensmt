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


#ifndef SIGPAIR_H
#define SIGPAIR_H

#include "Map.h"
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
