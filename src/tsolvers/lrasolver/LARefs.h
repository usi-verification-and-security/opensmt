#ifndef LABOUNDREFS_H
#define LABOUNDREFS_H
#include "IntTypes.h"
#include <ostream>

struct LABoundListRef
{
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const LABoundListRef& a1, const LABoundListRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const LABoundListRef& a1, const LABoundListRef& a2) { return a1.x != a2.x; }
};

static struct LABoundListRef LABoundListRef_Undef = {INT32_MAX};

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

static struct LABoundRef LABoundRef_Undef = {INT32_MAX};
static struct LABoundRef LABoundRef_Infty = { 0 };

struct LVRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const LVRef& a1, const LVRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const LVRef& a1, const LVRef& a2) { return a1.x != a2.x; }
};

struct LVRefHash {
    uint32_t operator() (const LVRef& s) const {return (uint32_t)s.x/8; }
};

static struct LVRef LVRef_Undef = { INT32_MAX };

#endif
