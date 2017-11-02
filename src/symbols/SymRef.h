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

#ifndef OPENSMT_SYMREF_H
#define OPENSMT_SYMREF_H

#include "Map.h"

struct SymRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const SymRef& a1, const SymRef& a2) {return a1.x == a2.x; }
    inline friend bool operator!= (const SymRef& a1, const SymRef& a2) {return a1.x != a2.x; }
};

static struct SymRef SymRef_Undef = {INT32_MAX};
static struct SymRef SymRef_Nil   = {INT32_MAX-1};

struct SymRefHash {
    uint32_t operator () (const SymRef& s) const {
        return (uint32_t)s.x; }
};

template <>
struct Equal<const SymRef> {
    bool operator() (const SymRef& s1, const SymRef& s2) { return s1 == s2; }
};

#endif //OPENSMT_SYMREF_H
