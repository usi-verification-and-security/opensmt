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

enum class SymbolProperty : char {
    None, LeftAssoc, RightAssoc, Chainable, Pairwise
};

struct SymbolConfig {
    bool isInterpreted;
    bool commutes;
    bool noScoping;
    SymbolProperty prop;
};

namespace SymConf {
    constexpr auto Default = SymbolConfig{false, false, false, SymbolProperty::None};
    constexpr auto Interpreted = SymbolConfig{true, false, false, SymbolProperty::None};
    constexpr auto LeftAssoc = SymbolConfig{false, false, false, SymbolProperty::LeftAssoc};
    constexpr auto RightAssoc = SymbolConfig{false, false, false, SymbolProperty::RightAssoc};
    constexpr auto Chainable = SymbolConfig{false, false, false, SymbolProperty::Chainable};
    constexpr auto Pairwise = SymbolConfig{false, false, false, SymbolProperty::Pairwise};
    constexpr auto NoScopingLeftAssoc = SymbolConfig{true, false, true, SymbolProperty::LeftAssoc};
    constexpr auto NoScopingRightAssoc = SymbolConfig{true, false, true, SymbolProperty::RightAssoc};
    constexpr auto NoScopingPairwise = SymbolConfig{true, false, true, SymbolProperty::Pairwise};
    constexpr auto NoScopingChainable = SymbolConfig{true, false, true, SymbolProperty::Chainable};
    constexpr auto NoScoping = SymbolConfig{true, false, true, SymbolProperty::None};
    constexpr auto CommutativeNoScopingLeftAssoc = SymbolConfig{true, true, true, SymbolProperty::LeftAssoc};
    constexpr auto CommutativeNoScopingChainable = SymbolConfig{true, true, true, SymbolProperty::Chainable};
    constexpr auto CommutativeNoScopingPairwise = SymbolConfig{true, true, true, SymbolProperty::Pairwise};
}

enum class SymbolMatcher : char {
    Any, Interpreted, Uninterpreted
};

// args[0].sort is the return sort, rest are arguments.
class Symbol {
    struct Header {
        unsigned type       : 3;
        unsigned commutes   : 1;
        unsigned noscoping  : 1;
        unsigned interpreted: 1;
        unsigned size       : 26;

        Header(unsigned _size, SymbolConfig const & sc)
            : type(static_cast<unsigned>(sc.prop))
            , commutes(sc.commutes)
            , noscoping(sc.noScoping)
            , interpreted(sc.isInterpreted)
            , size(_size)
        { }
    };
    const Header header;
    SymId                               id;
    // This has to be the last
    union { SRef sort; SymRef rel;  }   args[0];

    friend class SymbolAllocator;
    friend class SymStore;
    // Note: do not use directly (no memory allocation for args)

    Symbol(vec<SRef> const & ps, SymbolConfig const & config)
        : header(ps.size(), config)
    {
        assert(config.prop != SymbolProperty::LeftAssoc or nargs() == 2);
        assert(config.prop != SymbolProperty::RightAssoc or nargs() == 2);
        for (int i = 0; i < ps.size(); i++) args[i].sort = ps[i];
    }

  public:
    int      size        ()      const   { return static_cast<int>(header.size); }
    SRef     operator [] (int i) const   { return args[i+1].sort; }
    /**
     * @note The function is unsafe: if used in a loop, the loop should in *absolutely no case* build new symbols in the same Symbol allocator
     * @return A pointer to the first child of the symbol
     */
    SRef const * begin   ()      const   { return (SRef*)(args + 1); }
    /**
     * @note The function is unsafe: if used in a loop, the loop should in *absolutely no case* build new symbols in the same Symbol allocator
     * @return A pointer to right past the last child of the symbol
     */
    SRef const * end     ()      const   { return (SRef*)(args + size()); }
    SRef     rsort       ()      const   { return args[0].sort; }
    bool     commutes    ()      const   { return header.commutes; }
    SymRef   relocation  ()      const   { return args[0].rel; }
    SymbolProperty type  ()      const   { return static_cast<SymbolProperty>(header.type); }
    bool     left_assoc  ()      const   { return static_cast<SymbolProperty>(header.type) == SymbolProperty::LeftAssoc; }
    bool     right_assoc ()      const   { return static_cast<SymbolProperty>(header.type) == SymbolProperty::RightAssoc; }
    bool     chainable   ()      const   { return static_cast<SymbolProperty>(header.type) == SymbolProperty::Chainable; }
    bool     pairwise    ()      const   { return static_cast<SymbolProperty>(header.type) == SymbolProperty::Pairwise; }
    bool     noScoping   ()      const   { return header.noscoping; }
    uint32_t nargs       ()      const   { return size() - 1; }

    int      getId() const { return id; }
    void     setId(int i) { id = i; }
    bool     isInterpreted() const       { return header.interpreted; }

    bool matches(SymbolMatcher matcher) const {
        switch (matcher) {
            case SymbolMatcher::Interpreted:
                return isInterpreted();
            case SymbolMatcher::Uninterpreted:
                return not isInterpreted();
            case SymbolMatcher::Any:
            default:
                return true;
        }
    }
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

    SymRef alloc(vec<SRef> const & ps, SymbolConfig const & sc)
    {
        assert(sizeof(SRef)     == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));

        uint32_t v = RegionAllocator<uint32_t>::alloc(symWord32Size(ps.size()));
        SymRef symid;
        symid.x = v;

        new (lea(symid)) Symbol(ps, sc);
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
