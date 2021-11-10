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
#include "SSort.h"

#include "SymRef.h"

typedef uint32_t SymId; // Used as an array index

// args[0].sort is the return sort, rest are arguments.
class Symbol {
    struct {
        unsigned type       : 3;
        unsigned commutes   : 1;
        unsigned noscoping  : 1;
        unsigned constant   : 1;
        unsigned interpreted: 1;
        unsigned size       : 25; }     header;
    SymId                               id;
    // This has to be the last
    union { SRef sort; SymRef rel;  }   args[0];

    friend class SymbolAllocator;
    friend class SymStore;
    // Note: do not use directly (no memory allocation for args)
    Symbol(vec<SRef> const & ps) {
        header.type      = 0;
        header.commutes  = 0;
        header.noscoping = 0;           // This is an optimization to avoid expensive name lookup on logic operations
        header.constant  = false;
        header.interpreted = false;
        header.size      = ps.size();

        for (int i = 0; i < ps.size(); i++) args[i].sort = ps[i];
    }

  public:
    int      size        ()      const   { return header.size; }
    SRef     operator [] (int i) const   { return args[i+1].sort; }
    /**
     * @note The function is unsafe: if used in a loop, the loop should in *absolutely no case* build new symbols in the same Symbol allocator
     * @return A pointer to the first child of the symbol
     */
    SRef const * begin   ()      const   { return (SRef*)(args + 1); }
    /**
     * @note The function is unsafe: if used in a loop, the loop should in *absolutely no case* build new symbols in the same Symbol allocator
     * @return A pointer to the last child of the symbol
     */
    SRef const * end     ()      const   { return (SRef*)(args + size()); }
    SRef     rsort       ()      const   { return args[0].sort; }
    bool     commutes    ()      const   { return header.commutes; }
    SymRef   relocation  ()      const   { return args[0].rel; }
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
    bool     isInterpreted() const       { return header.interpreted; }

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

    SymRef alloc(vec<SRef> const & ps)
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
};

#endif
