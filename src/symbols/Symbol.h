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


// Strongly MiniSat inspired implementation for Symbols
#ifndef SYMBOL_H
#define SYMBOL_H

#include "Vec.h"
#include "Alloc.h"
#include "sorts/Sort.h"
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

typedef uint32_t SymId; // Used as an array index

// args[0].sort is the return sort, rest are arguments.
class Symbol {
    struct {
        unsigned type       : 3;
        unsigned learnt     : 1;
        unsigned commutes   : 1;
        unsigned reloced    : 1;
        unsigned noscoping  : 1;
        unsigned constant   : 1;
        unsigned size       : 24; }     header;
    SymId                               id;
    // This has to be the last
    union { SRef sort; SymRef rel;  }   args[0];

#ifdef PEDANTIC_DEBUG
    void compare(Symbol& other) {
        assert(header.type == other.header.type);
        assert(header.learnt == other.header.learnt);
        assert(header.commutes == other.header.commutes);
        assert(header.reloced == other.header.reloced);
        assert(header.noscoping == other.header.noscoping);
        assert(header.constant == other.header.constant);
        assert(header.size == other.header.size);
        for (int i = 0; i < header.size; i++)
            assert(args[i].sort.x == other.args[i].sort.x);
        assert(id == other.id);
    }
#endif

    friend class SymAllocator;
    friend class SymStore;
  public:
    // Note: do not use directly (no memory allocation for args)
    Symbol(const vec<SRef>& ps) {
        header.type      = 0;
        header.learnt    = 0;
        header.commutes  = 0;
        header.reloced   = 0;
        header.noscoping = 0;           // This is an optimization to avoid expensive name lookup on logic operations
        header.constant  = false;
        header.size      = ps.size();

        for (int i = 0; i < ps.size(); i++) args[i].sort = ps[i]; }
  public:

    // -- use this as a wrapper:
    Symbol* Symbol_new(vec<SRef>& ps, bool left_assoc = false, bool right_assoc = false, bool chainable = false, bool pairwise = false) {
        assert(sizeof(SRef) == sizeof(uint32_t));
        void* mem = malloc(sizeof(header) + sizeof(SymId) + sizeof(uint32_t)*ps.size());
        assert(left_assoc + right_assoc + chainable + pairwise <= 1);
        if (left_assoc == true)
            header.type = 1;
        else if (right_assoc == true)
            header.type = 2;
        else if (chainable == true)
            header.type = 3;
        else if (pairwise == true)
            header.type = 4;
        return new (mem) Symbol(ps); }

    int      size        ()      const   { return header.size; }
    SRef     operator [] (int i) const   { return args[i+1].sort; }
    SRef     rsort       ()      const   { return args[0].sort; }
    bool     commutes    ()      const   { return header.commutes; }
    bool     reloced     ()      const   { return header.reloced; }
    SymRef   relocation  ()      const   { return args[0].rel; }
    bool     learnt      ()      const   { return header.learnt; }
    void     relocate    (SymRef t)      { header.reloced = 1; args[0].rel = t; }
    uint32_t type        ()      const   { return header.type; }
    void     type        (uint32_t m)    { header.type = m; }
    bool     left_assoc  ()      const   { return header.type == 1; }
    bool     right_assoc ()      const   { return header.type == 2; }
    bool     chainable   ()      const   { return header.type == 3; }
    bool     pairwise    ()      const   { return header.type == 4; }
    bool     noScoping   ()      const   { return header.noscoping; }
    uint32_t nargs       ()      const   { return size() - 1; }
    bool     isConstant  ()      const   { return nargs() == 0 && header.constant; }

    bool     setLeftAssoc ()             { if (header.type != 0) return false; return (header.type = 1); }
    bool     setRightAssoc()             { if (header.type != 0) return false; return (header.type = 2); }
    bool     setChainable ()             { if (header.type != 0) return false; return (header.type = 3); }
    bool     setPairwise  ()             { if (header.type != 0) return false; return (header.type = 4); }
    void     setNoScoping ()             { header.noscoping = 1; }
    void     setCommutes  ()             { header.commutes  = 1; }

    int      getId() const { return id; }
    void     setId(int i) { id = i; }

};


class SymbolAllocator : public RegionAllocator<uint32_t>
{
    static int symWord32Size(int size){
        return (sizeof(Symbol) + (sizeof(SRef) * size )) / sizeof(uint32_t); }
 public:
    bool extra_term_field;

    SymbolAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), extra_term_field(false){}
    SymbolAllocator() : extra_term_field(false){}

    void moveTo(SymbolAllocator& to){
        to.extra_term_field = extra_term_field;
        RegionAllocator<uint32_t>::moveTo(to); }

    SymRef alloc(Symbol& ps, bool)
    {
        assert(false);
        assert(sizeof(SRef)     == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));

        uint32_t v = RegionAllocator<uint32_t>::alloc(symWord32Size(ps.size()));
        SymRef symid;
        symid.x = v;

        new (lea(symid)) Symbol(ps);
        return symid;
    }

    SymRef alloc(const vec<SRef>& ps, bool)
    {
        assert(sizeof(SRef)     == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));

        uint32_t v = RegionAllocator<uint32_t>::alloc(symWord32Size(ps.size()));
        SymRef symid;
        symid.x = v;

        new (lea(symid)) Symbol(ps);
        return symid;
    }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Symbol&       operator[](SymRef r)        { return (Symbol&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Symbol& operator[](SymRef r) const  { return (Symbol&)RegionAllocator<uint32_t>::operator[](r.x); }
    Symbol*       lea       (SymRef r)        { return (Symbol*)RegionAllocator<uint32_t>::lea(r.x); }
    const Symbol* lea       (SymRef r) const  { return (Symbol*)RegionAllocator<uint32_t>::lea(r.x); }
    SymRef        ael       (const Symbol* t) { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); SymRef rf; rf.x = r; return rf; }

    void free(SymRef symid)
    {
        Symbol& s = operator[](symid);
        RegionAllocator<uint32_t>::free(symWord32Size(s.size()));
    }

    void reloc(SymRef& symr, SymbolAllocator& to)
    {
        Symbol& s = operator[](symr);

        if (s.reloced()) { symr = s.relocation(); return; }

        symr = to.alloc(s, s.learnt());
        s.relocate(symr);

        // Copy extra data-fields:
        to[symr].type(s.type());
//        if (to[tr].learnt())         to[tr].activity() = t.activity();
//        else if (to[tr].has_extra()) to[tr].calcAbstraction();
    }
};

#endif
