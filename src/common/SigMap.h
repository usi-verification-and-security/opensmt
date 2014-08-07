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
