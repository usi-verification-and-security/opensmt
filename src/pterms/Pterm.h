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

// Strongly MiniSat inspired implementation for proper terms
#ifndef PTERM_H
#define PTERM_H

#include "PtStructs.h"

#include <minisat/core/SolverTypes.h>
#include <minisat/mtl/Sort.h>
#include <minisat/mtl/Vec.h>
#include <symbols/SymRef.h>

namespace opensmt {
// A key used for pterm resolve lookups
struct PTLKey {
    SymRef sym;
    vec<PTRef> args;
    friend bool operator==(PTLKey const & k1, PTLKey const & k2) {
        if (k1.sym != k2.sym) return false;
        if (k1.args.size() != k2.args.size()) return false;
        int i;
        for (i = 0; i < k1.args.size(); i++)
            if (k1.args[i] != k2.args[i]) break;
        return i == k1.args.size();
    }
};

struct PTLHash {
    uint32_t operator()(PTLKey const & s) const {
        uint32_t v = (uint32_t)s.sym.x;
        for (int i = 0; i < s.args.size(); i++) {
            v += (uint32_t)s.args[i].x;
        }
        return v;
    }
};

// typedef uint32_t TRef;
struct PTId {
    uint32_t x;
    inline friend bool operator==(PTId const & a1, PTId const & a2) { return a1.x == a2.x; }
    inline friend bool operator!=(PTId const & a1, PTId const & a2) { return a1.x != a2.x; }
    inline friend bool operator<(PTId const & a1, PTId const & a2) { return a1.x > a2.x; }
    inline friend uint32_t Idx(PTId p) { return p.x; }
};

class Pterm {
public:
    // forbid any copies or moves
    Pterm() = delete;
    Pterm(Pterm const &) = delete;
    Pterm(Pterm &&) = delete;
    Pterm operator=(Pterm) = delete;
    Pterm operator=(Pterm const &) = delete;
    Pterm operator=(Pterm &) = delete;
    Pterm operator=(Pterm &&) = delete;

    int size() const { return static_cast<int>(header.size); }

    PTRef operator[](int i) const {
        assert(i < size());
        return args[i];
    }

    SymRef symb() const { return sym; }
    bool has_extra() const { return false; }
    bool reloced() const { return header.reloced; }
    PTRef relocation() const { return args[0]; }
    void relocate(PTRef t) {
        header.reloced = 1;
        args[0] = t;
    }
    uint32_t type() const { return header.type; }
    void type(uint32_t m) { header.type = m; }
    bool left_assoc() const { return header.type == 1; }
    bool right_assoc() const { return header.type == 2; }
    bool chainable() const { return header.type == 3; }
    bool pairwise() const { return header.type == 4; }
    bool noScoping() const { return header.noscoping; }
    uint32_t nargs() const { return size(); }

    bool setLeftAssoc() {
        if (header.type != 0) return false;
        return (header.type = 1);
    }
    bool setRightAssoc() {
        if (header.type != 0) return false;
        return (header.type = 2);
    }
    bool setChainable() {
        if (header.type != 0) return false;
        return (header.type = 3);
    }
    bool setPairwise() {
        if (header.type != 0) return false;
        return (header.type = 4);
    }
    void setNoScoping() { header.noscoping = 1; }

    PTId getId() const { return id; }
    void setId(int i) { id.x = i; }

    void shrink(int s) { header.size -= s; }

    /**
     * @note The function is unsafe: if used in a loop, the loop should in *absolutely no case* build new terms in
     * the same Pterm allocator
     * @return A pointer to the first child of the term
     */
    PTRef const * begin() const { return args; }
    /**
     * @note The function is unsafe: if used in a loop, the loop should in *absolutely no case* build new terms in
     * the same Pterm allocator
     * @return A pointer to right past the last child of the term
     */
    PTRef const * end() const { return args + size(); }
#ifdef PEDANTIC_DEBUG
    void compare(Pterm & other) {
        assert(header.type == other.header.type);
        assert(header.has_extra == other.header.has_extra);
        assert(header.reloced == other.header.reloced);
        assert(header.noscoping == other.header.noscoping);
        assert(header.size == other.header.size);
        assert(id == other.id);
        assert(sym == other.sym);
        for (int i = 0; i < header.size; i++)
            assert(args[i] == other.args[i]);
    }
#endif
private:
    friend class PtermAllocator;
    friend void ptermSort(Pterm &);

    // MB: Constructor is private to forbid any use outside PtermAllocator, which is a friend
    Pterm(SymRef const sym_, vec<PTRef> const & ps) : sym(sym_) {
        header.type = 0;
        header.has_extra = 0;
        header.reloced = 0;
        header.noscoping = 0; // This is an optimization to avoid expensive name lookup on logic operations
        header.size = ps.size();

        for (int i = 0; i < ps.size(); i++) {
            args[i] = ps[i];
        }
    }

    struct {
        unsigned type : 3;
        unsigned has_extra : 1;
        unsigned reloced : 1;
        unsigned noscoping : 1;
        unsigned size : 26;
    } header;
    PTId id;
    SymRef sym;
    PTRef args[0]; // Either the terms or the relocation reference
};

class PtPair {
public:
    PTRef x;
    PTRef y;
    PtPair(PTRef x_, PTRef y_) : x(x_), y(y_) {}
};

class PtChild {
public:
    PTRef tr;
    PTRef parent;
    int pos;
    PtChild(PTRef tr_, PTRef parent_, int pos_) : tr(tr_), parent(parent_), pos(pos_) {}
    PtChild() : tr(PTRef_Undef), parent(PTRef_Undef), pos(-1) {}
    inline friend bool operator==(PtChild const & a1, PtChild const & a2) {
        return (a1.tr == a2.tr) && (a1.parent == a2.parent) && (a1.pos == a2.pos);
    }
    inline friend bool operator!=(PtChild const & a1, PtChild const & a2) {
        return (a1.tr != a2.tr) || (a1.parent != a2.parent) || (a1.pos != a2.pos);
    }
};

struct PtChildHash {
    uint32_t operator()(PtChild const & s) const { return (uint32_t)s.tr.x + (uint32_t)s.parent.x + (uint32_t)s.pos; }
};

class PtermAllocator : public RegionAllocator<uint32_t> {
public:
    PtermAllocator(uint32_t start_cap) : RegionAllocator(start_cap), n_terms(0) {}
    PtermAllocator() : n_terms(0) {}

    uint32_t getNumTerms() const { return n_terms; }

    void moveTo(PtermAllocator & to) {
        to.n_terms = n_terms;
        RegionAllocator::moveTo(to);
    }

    PTRef alloc(SymRef const sym, vec<PTRef> const & ps) {
        assert(sizeof(PTRef) == sizeof(uint32_t));

        uint32_t v = RegionAllocator::alloc(ptermWord32Size(ps.size()));
        PTRef tid = {v};
        new (lea(tid)) Pterm(sym, ps);
        operator[](tid).setId(n_terms++);

        return tid;
    }

    PTRef alloc(Pterm &, bool) {
        assert(false);
        return PTRef_Undef;
    }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Pterm & operator[](PTRef r) { return reinterpret_cast<Pterm &>(RegionAllocator::operator[](r.x)); }
    Pterm const & operator[](PTRef r) const {
        return reinterpret_cast<Pterm const &>(RegionAllocator::operator[](r.x));
    }
    Pterm * lea(PTRef r) { return reinterpret_cast<Pterm *>(RegionAllocator::lea(r.x)); }
    Pterm const * lea(PTRef r) const { return reinterpret_cast<Pterm const *>(RegionAllocator::lea(r.x)); }
    PTRef ael(Pterm const * t) {
        RegionAllocator::Ref r = RegionAllocator::ael((uint32_t *)t);
        PTRef rf;
        rf.x = r;
        return rf;
    }

    void free(PTRef tid) {
        Pterm const & t = operator[](tid);
        RegionAllocator::free(ptermWord32Size(t.size()));
    }

    void reloc(PTRef & tr, PtermAllocator & to);
    /*{
        Pterm& t = operator[](tr);

        if (t.reloced()) { tr = t.relocation(); return; }

        tr = to.alloc(t, false);
        t.relocate(tr);

        // Copy extra data-fields:
        to[tr].type(t.type());
//        if (to[tr].learnt())         to[tr].activity() = t.activity();
//        else if (to[tr].has_extra()) to[tr].calcAbstraction();
    }*/
private:
    friend class PtStore;

    uint32_t n_terms;
    static int ptermWord32Size(int size) { return (sizeof(Pterm) + (sizeof(PTRef) * size)) / sizeof(uint32_t); }
};
} // namespace opensmt

#endif
