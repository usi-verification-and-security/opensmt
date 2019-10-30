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


#ifndef STRINGMAP_H
#define STRINGMAP_H

#include "Map.h"

//===================================================================================================
// Specializations for string hashing (Map from mtl)
//

struct StringHash {
    uint32_t operator () (const char* s) const {
        // http://www.cse.yorku.ca/~oz/hash.html
        size_t h = 5381;
        int c;
        while ((c = *s++))
            h = ((h << 5) + h) + c;
        return h;
    }
};

template <>
struct Equal<const char*> {
    bool operator() (const char* s1, const char* s2) const {
        int i = 0;
        for (i = 0; s1[i] != '\0' && s2[i] != '\0'; i++)
            if (s1[i] != s2[i]) break;
        return (s1[i] == 0 && s2[i] == 0); }
};

#endif
