#ifndef LABOUNDREFS_H
#define LABOUNDREFS_H
#include "IntTypes.h"
#include <ostream>
#include <cassert>

struct LABoundListRef
{
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const LABoundListRef& a1, const LABoundListRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const LABoundListRef& a1, const LABoundListRef& a2) { return a1.x != a2.x; }
};

const struct LABoundListRef LABoundListRef_Undef = {INT32_MAX};

struct BoundT {
    char t;
    bool operator== (const BoundT& o) const { return o.t == t; }
    bool operator!= (const BoundT& o) const { return o.t != t; }
    BoundT operator~ () const { return { (char)(1-t) }; }
};

const BoundT bound_l = { 0 };
const BoundT bound_u = { 1 };

struct LABoundRef
{
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const LABoundRef& a1, const LABoundRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const LABoundRef& a1, const LABoundRef& a2) { return a1.x != a2.x; }
};

const struct LABoundRef LABoundRef_Undef = {INT32_MAX};
const struct LABoundRef LABoundRef_Infty = { 0 };

struct LVRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const LVRef& a1, const LVRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const LVRef& a1, const LVRef& a2) { return a1.x != a2.x; }
};

inline unsigned getVarId(LVRef ref) { return ref.x;}
// For debugging
inline char* printVar (LVRef r) { char* str; int written = asprintf(&str, "v%d", r.x); assert(written >= 0); (void)written; return str; }

struct LVRefHash {
    uint32_t operator() (const LVRef& s) const {return s.x; }
};

struct LVRefComp {
    bool operator()(LVRef a, LVRef b) const { return a.x < b.x; }
};

const struct LVRef LVRef_Undef = { INT32_MAX };

#endif
