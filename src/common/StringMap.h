/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/


#ifndef STRINGMAP_H
#define STRINGMAP_H

#include "minisat/mtl/Map.h"

//===================================================================================================
// Specializations for string hashing (Map from mtl)
//

struct StringHash {
    uint32_t operator () (const char* s) const {
        uint32_t v = 0;
        for (int i = 0; s[i] != '\0'; i++) v += (uint32_t)s[i];
    return v; }
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
