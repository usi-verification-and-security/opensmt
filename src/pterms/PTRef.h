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

#ifndef OPENSMT_PTREF_H
#define OPENSMT_PTREF_H

#include <functional>

struct PTRef {
    uint32_t x;
    inline friend bool operator== (PTRef a1, PTRef a2)   { return a1.x == a2.x; }
    inline friend bool operator!= (PTRef a1, PTRef a2)   { return a1.x != a2.x; }
    inline friend bool operator<  (PTRef a1, PTRef a2)   { return a1.x < a2.x;  }
};

const struct PTRef PTRef_Undef = {INT32_MAX};

struct PTRefHash {
    uint32_t operator () (PTRef s) const { return s.x; }
};

struct PTRefPairHash {
    std::size_t operator () (std::pair<PTRef, PTRef> p) const {
        std::hash<uint32_t> hasher;
        return (hasher(p.first.x) ^ hasher(p.second.x));
    }
};

#endif //OPENSMT_PTREF_H
