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
#include "Alloc.h"
#include "Symbol.h"
#include "Sort.h"
#include "SolverTypes.h"

//typedef RegionAllocator<uint32_t>::Ref PTRef;

struct PTRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const PTRef& a1, const PTRef& a2)   { return a1.x == a2.x; }
    inline friend bool operator!= (const PTRef& a1, const PTRef& a2)   { return a1.x != a2.x; }
    inline friend bool operator< (const PTRef& a1, const PTRef& a2)    { return a1.x > a2.x;  }
};

static struct PTRef PTRef_Undef = {INT32_MAX};

struct PTRefHash {
    uint32_t operator () (const PTRef& s) const {
        return (uint32_t)s.x; }
};


template <>
struct Equal<const PTRef> {
    bool operator() (const PTRef& s1, const PTRef& s2) const { return s1 == s2; }
};

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

/*
template <>
struct Equal<const PTLKey> {
    bool operator() (const PTLKey& k1, const PTLKey& k2) {
        if (k1.sym != k2.sym) return false;
        if (k1.args.size() != k2.args.size()) return false;
        int i;
        for (i = 0; i < k1.args.size(); i++)
            if (k1.args[i] != k2.args[i]) break;
        return i == k1.args.size();
    }
};
*/

class PtAsgn {
  public:
    PTRef tr;
    lbool sgn;
    PtAsgn(PTRef tr_, lbool sgn_) : tr(tr_), sgn(sgn_) {}
    PtAsgn() : tr(PTRef_Undef), sgn(l_Undef) {}
};

static class PtAsgn PtAsgn_Undef(PTRef_Undef, l_Undef);

class PtAsgn_reason {
  public:
    PTRef tr;
    PTRef reason;
    lbool sgn;
    PtAsgn_reason(PTRef tr_, lbool sgn_, PTRef reason_)
         : tr(tr_)
         , reason(reason_)
         , sgn(sgn_)
         {}
    PtAsgn_reason() : tr(PTRef_Undef), reason(PTRef_Undef), sgn(l_Undef) {}
};

static class PtAsgn_reason PtAsgn_reason_Undef(PTRef_Undef, l_Undef, PTRef_Undef);


//typedef uint32_t TRef;
typedef uint32_t PTId; // Used as an array index

class Pterm {
    struct {
        unsigned type       : 3;
        unsigned has_extra  : 1;
        unsigned reloced    : 1;
        unsigned noscoping  : 1;
        unsigned size       : 26; }     header;
    PTId                                id;
    SymRef                              sym;
#ifdef TERMS_HAVE_EXPLANATIONS
    PtAsgn      exp_reason;
    PTRef       exp_parent;
    PTRef       exp_root;
    int         exp_class_size;
    int         exp_time_stamp;
#endif
    // This has to be the last
    PTRef                               args[0]; // Either the terms or the relocation reference


    friend class PtermAllocator;
    friend class PTStore;
    friend void termSort(Pterm&);
    friend class Logic;
  public:

#ifdef TERMS_HAVE_EXPLANATIONS
    PtAsgn getExpReason       () const { return exp_reason; }
    PTRef  getExpParent       () const { return exp_parent; }
    PTRef  getExpRoot         () const { return exp_root; }
    int    getExpClassSize    () const { return exp_class_size; }
    int    getExpTimeStamp    () const { return exp_time_stamp; }

    void setExpReason     (PtAsgn r)     { exp_reason = r; }
    void setExpParent     (PTRef r)      { exp_parent = r; }
    void setExpRoot       (PTRef r)      { exp_root   = r; }
    void setExpClassSize  (const int s)  { exp_class_size   = s; }
    void setExpTimeStamp  (const int t)  { exp_time_stamp   = t; }
#endif

    // Note: do not use directly (no memory allocation for args)
#ifdef TERMS_HAVE_EXPLANATIONS
    Pterm(const SymRef sym_, const vec<PTRef>& ps, PTRef t) : sym(sym_) {
#else
    Pterm(const SymRef sym_, const vec<PTRef>& ps) : sym(sym_) {
#endif
        header.type      = 0;
        header.has_extra = 0;
        header.reloced   = 0;
        header.noscoping = 0;           // This is an optimization to avoid expensive name lookup on logic operations
        header.size      = ps.size();

        for (int i = 0; i < ps.size(); i++) args[i] = ps[i];
#ifdef TERMS_HAVE_EXPLANATIONS
        setExpReason(PtAsgn(PTRef_Undef, l_Undef));
        setExpParent(PTRef_Undef);
        setExpRoot(t);
        setExpClassSize(1);
        setExpTimeStamp(0);
#endif
    }
    Pterm() {
        header.type      = 0;
        header.has_extra = 0;
        header.reloced   = 0;
        header.noscoping = 0;           // This is an optimization to avoid expensive name lookup on logic operations
        header.size      = 0;

    }

/*
    // -- use this as a wrapper:
    Pterm* Pterm_new(SymRef sym, vec<PTRef>& ps, bool left_assoc = false, bool right_assoc = false, bool chainable = false, bool pairwise = false) {
        assert(sizeof(PTRef) == sizeof(uint32_t));
        assert(sizeof(PTId)  == sizeof(uint32_t));
        assert(sizeof(SymRef)  == sizeof(uint32_t));
        void* mem = malloc(sizeof(header) + sizeof(PTId) + +sizeof(SymRef) + sizeof(PTRef)*ps.size());

        assert(left_assoc + right_assoc + chainable + pairwise <= 1);
        if (left_assoc == true)
            header.type = 1;
        else if (right_assoc == true)
            header.type = 2;
        else if (chainable == true)
            header.type = 3;
        else if (pairwise == true)
            header.type = 4;
        return new (mem) Pterm(sym, ps); }
*/
    Pterm    operator=   (Pterm t1)      { assert(false); return *this; }

    int      size        ()      const   { return header.size; }
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

    int      getId() const { return id; }
    void     setId(int i) { id = i; }

    void     shrink(int s)               { header.size -= s; }
    void     copyTo(Pterm& to);
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
    PTId n_terms;
    static int ptermWord32Size(int size){
        return (sizeof(Pterm) + (sizeof(PTRef) * size )) / sizeof(uint32_t); }
 public:
    bool extra_term_field;

    PtermAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_terms(0), extra_term_field(false){}
    PtermAllocator() : n_terms(0), extra_term_field(false){}

    void moveTo(PtermAllocator& to){
        to.n_terms = n_terms;
        to.extra_term_field = extra_term_field;
        RegionAllocator<uint32_t>::moveTo(to); }

    PTRef alloc(const SymRef sym, const vec<PTRef>& ps, bool extra = false)
    {
        assert(sizeof(PTRef) == sizeof(uint32_t));

        uint32_t v = RegionAllocator<uint32_t>::alloc(ptermWord32Size(ps.size()));
        PTRef tid = {v};
#ifdef TERMS_HAVE_EXPLANATIONS
        new (lea(tid)) Pterm(sym, ps, tid);
#else
        new (lea(tid)) Pterm(sym, ps);
#endif
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
};

struct LessThan_PTRef {
    bool operator () (PTRef& x, PTRef& y) { return x.x < y.x; } };

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
