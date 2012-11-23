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
