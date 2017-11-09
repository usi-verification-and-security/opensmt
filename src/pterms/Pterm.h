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

#include "Vec.h"
#include "Sort.h"
#include "SolverTypes.h"
#include "SymRef.h"
#include "PtStructs.h"


// A key used for pterm resolve lookups
struct PTLKey {
    SymRef     sym;
    vec<PTRef> args;
    friend bool operator== (const PTLKey& k1, const PTLKey& k2) {
        if (k1.sym != k2.sym) return false;
        if (k1.args.size() != k2.args.size()) return false;
        int i;
        for (i = 0; i < k1.args.size(); i++)
            if (k1.args[i] != k2.args[i]) break;
        return i == k1.args.size();
    }
    void operator= (const PTLKey& k) {
        sym = k.sym;
        k.args.copyTo(args);
    }
};


struct PTLHash {
    uint32_t operator () (const PTLKey& s) const {
        uint32_t v = (uint32_t)s.sym.x;
        for (int i = 0; i < s.args.size(); i++)
            v += (uint32_t)s.args[i].x;
        return v; }
};

//typedef uint32_t TRef;
struct PTId {
    uint32_t x;
    inline friend bool operator== (const PTId& a1, const PTId& a2)   { return a1.x == a2.x; }
    inline friend bool operator!= (const PTId& a1, const PTId& a2)   { return a1.x != a2.x; }
    inline friend bool operator<  (const PTId& a1, const PTId& a2)   { return a1.x > a2.x;  }
    inline friend uint32_t Idx(PTId p) { return p.x; }
};

class Pterm {
    struct {
        unsigned type       : 3;
        unsigned has_extra  : 1;
        unsigned reloced    : 1;
        unsigned noscoping  : 1;
        unsigned size       : 26; }     header;
    PTId        id;
    SymRef      sym;
    Var         var;     // This is defined if the PTRef has a Boolean var associated with it
    PtAsgn      exp_reason;
    PTRef       exp_parent;
    PTRef       exp_root;
    int         exp_time_stamp;
    // This has to be the last
    PTRef       args[0]; // Either the terms or the relocation reference


    friend class PtermAllocator;
    friend class PTStore;
    friend void  termSort(Pterm&);
    friend class Logic;
  public:

    PtAsgn getExpReason       () const { return exp_reason; }
    PTRef  getExpParent       () const { return exp_parent; }
    PTRef  getExpRoot         () const { return exp_root; }
    int    getExpTimeStamp    () const { return exp_time_stamp; }

    void setExpReason     (PtAsgn r)     { exp_reason = r; }
    void setExpParent     (PTRef r)      { exp_parent = r; }
    void setExpRoot       (PTRef r)      { exp_root   = r; }
    void setExpTimeStamp  (const int t)  { exp_time_stamp   = t; }

    // Note: do not use directly (no memory allocation for args)
    Pterm(const SymRef sym_, const vec<PTRef>& ps, PTRef t) : sym(sym_) {
        header.type      = 0;
        header.has_extra = 0;
        header.reloced   = 0;
        header.noscoping = 0;           // This is an optimization to avoid expensive name lookup on logic operations
        header.size      = ps.size();

        var              = var_Undef;

        for (int i = 0; i < ps.size(); i++) args[i] = ps[i];
        setExpReason(PtAsgn(PTRef_Undef, l_Undef));
        setExpParent(PTRef_Undef);
        setExpRoot(t);
        setExpTimeStamp(0);
    }
    Pterm() {
        header.type      = 0;
        header.has_extra = 0;
        header.reloced   = 0;
        header.noscoping = 0;           // This is an optimization to avoid expensive name lookup on logic operations
        header.size      = 0;

        var              = var_Undef;

    }

    Pterm    operator=   (Pterm)         { assert(false); return *this; }

    int      size        ()          const   { return header.size; }

    const PTRef& operator [] (int i) const   { assert(i < size()); return args[i]; }
    PTRef&       operator [] (int i)         { assert(i < size()); return args[i]; }

    SymRef   symb        ()      const   { return sym; }
    bool     has_extra   ()      const   { return false; }
    bool     reloced     ()      const   { return header.reloced; }
    PTRef    relocation  ()      const   { return args[0]; }
    void     relocate    (PTRef t)       { header.reloced = 1; args[0] = t; }
    uint32_t type        ()      const   { return header.type; }
    void     type        (uint32_t m)    { header.type = m; }
    bool     left_assoc  ()      const   { return header.type == 1; }
    bool     right_assoc ()      const   { return header.type == 2; }
    bool     chainable   ()      const   { return header.type == 3; }
    bool     pairwise    ()      const   { return header.type == 4; }
    bool     noScoping   ()      const   { return header.noscoping; }
    uint32_t nargs       ()      const   { return size(); }

    bool     setLeftAssoc ()             { if (header.type != 0) return false; return (header.type = 1); }
    bool     setRightAssoc()             { if (header.type != 0) return false; return (header.type = 2); }
    bool     setChainable ()             { if (header.type != 0) return false; return (header.type = 3); }
    bool     setPairwise  ()             { if (header.type != 0) return false; return (header.type = 4); }
    void     setNoScoping ()             { header.noscoping = 1; }

    PTId     getId() const { return id; }
    void     setId(int i) { id.x = i; }

    void     setVar(Var v)   { var = v; }
    void     clearVar()      { var = var_Undef; }
    Var      getVar() const  { return var; }
    bool     hasVar() const  { return var != var_Undef; }

    void     shrink(int s)               { header.size -= s; }
    void     copyTo(Pterm& to);
#ifdef PEDANTIC_DEBUG
    void     compare(Pterm& other) {
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
    inline friend bool operator== (const PtChild& a1, const PtChild& a2)
        { return (a1.tr == a2.tr) && (a1.parent == a2.parent) && (a1.pos == a2.pos); }
    inline friend bool operator!= (const PtChild& a1, const PtChild& a2)
        { return (a1.tr != a2.tr) || (a1.parent != a2.parent) || (a1.pos != a2.pos); }
//    inline friend bool operator< (const PTRef& a1, const PTRef& a2)    { return a1.x < a2.x;  }
};

struct PtChildHash {
    uint32_t operator () (const PtChild& s) const {
        return (uint32_t)s.tr.x+(uint32_t)s.parent.x+(uint32_t)s.pos; }
};

class PtermAllocator : public RegionAllocator<uint32_t>
{
    uint32_t n_terms;
    void setNumTerms(int i) { n_terms = i; }
    static int ptermWord32Size(int size){
        return (sizeof(Pterm) + (sizeof(PTRef) * size )) / sizeof(uint32_t); }
 public:

    PtermAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_terms(0) {}
    PtermAllocator() : n_terms(0) {}

    int getNumTerms() const { return n_terms; }

    void moveTo(PtermAllocator& to){
        to.n_terms = n_terms;
        RegionAllocator<uint32_t>::moveTo(to); }

    PTRef alloc(const SymRef sym, const vec<PTRef>& ps, bool extra = false)
    {
        assert(sizeof(PTRef) == sizeof(uint32_t));

        uint32_t v = RegionAllocator<uint32_t>::alloc(ptermWord32Size(ps.size()));
        PTRef tid = {v};
        new (lea(tid)) Pterm(sym, ps, tid);
        operator[](tid).setId(n_terms++);

        return tid;
    }

    PTRef alloc(Pterm&, bool) { assert(false); return PTRef_Undef; }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Pterm&       operator[](PTRef r)         { return (Pterm&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Pterm& operator[](PTRef r) const   { return (Pterm&)RegionAllocator<uint32_t>::operator[](r.x); }
    Pterm*       lea       (PTRef r)         { return (Pterm*)RegionAllocator<uint32_t>::lea(r.x); }
    const Pterm* lea       (PTRef r) const   { return (Pterm*)RegionAllocator<uint32_t>::lea(r.x); }
    PTRef        ael       (const Pterm* t)  { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); PTRef rf; rf.x = r; return rf; }

    void free(PTRef tid)
    {
        Pterm& t = operator[](tid);
        RegionAllocator<uint32_t>::free(ptermWord32Size(t.size()));
    }

    void reloc(PTRef& tr, PtermAllocator& to)
    {
        Pterm& t = operator[](tr);

        if (t.reloced()) { tr = t.relocation(); return; }

        tr = to.alloc(t, false);
        t.relocate(tr);

        // Copy extra data-fields:
        to[tr].type(t.type());
//        if (to[tr].learnt())         to[tr].activity() = t.activity();
//        else if (to[tr].has_extra()) to[tr].calcAbstraction();
    }
    friend class PtStore;
};

inline void termSort(Pterm& t) {
//    PTRef                               args[0]; // Either the terms or the relocation reference
    sort(t.args, t.size(), LessThan_PTRef()); }

inline bool isSorted(vec<PTRef>& args) {
    LessThan_PTRef lt;
    if (args.size() == 0) return true;
    PTRef c = args[0];
    for (int i = 1; i < args.size(); i++) {
        if (!lt.operator()(c, args[i])) return false;
        c = args[i];
    }
    return true;
}
#endif
