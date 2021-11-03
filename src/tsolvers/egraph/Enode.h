/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                          2008 - 2012 Roberto Bruttomesso

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

#ifndef ENODE_H
#define ENODE_H

#include "Vec.h"
#include "Alloc.h"

#include "PtStructs.h"
#include "SymRef.h"
#include "TypeUtils.h"
#include "CgTypes.h"
#include "SigMap.h"


struct ERef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator<  (const ERef& a1, const ERef& a2) {return a1.x < a2.x;  }
    inline friend bool operator== (const ERef& a1, const ERef& a2) {return a1.x == a2.x; }
    inline friend bool operator!= (const ERef& a1, const ERef& a2) {return a1.x != a2.x; }
};
static struct ERef ERef_Undef = {UINT32_MAX};

struct UseVectorIndex {
    uint32_t x;
    inline friend bool operator== (const UseVectorIndex& a1, const UseVectorIndex& a2) {return a1.x == a2.x; }
    inline friend bool operator!= (const UseVectorIndex& a1, const UseVectorIndex& a2) {return a1.x != a2.x; }
    static UseVectorIndex NotValidIndex;
};

static_assert(sizeof(ERef) == sizeof(UseVectorIndex));

inline void swap(ERef & y, ERef & z) { ERef tmp = y; y = z; z = tmp; }

using CgId = uint32_t;
using enodeid_t = int;


//
// Data structure used to store forbid lists
//

struct ELRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const ELRef& a1, const ELRef& a2) {return a1.x == a2.x; }
    inline friend bool operator!= (const ELRef& a1, const ELRef& a2) {return a1.x != a2.x; }
};

static struct ELRef ELRef_Undef = {UINT32_MAX};

class EnodeAllocator;

class Enode final
{
private:
    static uint32_t cgid_ctr;

    ERef    root;           // The root of this enode's equivalence class
    cgId    cid;            // The congruence id of the enode (never changes)
    ERef    eq_next;           // Next node in this enode's equivalence class
    int     eq_size;           // Size of this enode's equivalence class
    PTRef   pterm;          // The corresponding pterm
    ELRef   forbid;         // List of unmergeable Enodes
    dist_t  dist_classes;   // The bit vector for distinction classes

    // fields related to explanation
    PtAsgn      exp_reason;
    ERef        exp_parent;
    ERef        exp_root;
    int         exp_time_stamp;

    // Term representation
    SymRef symb;
    uint32_t argSize;

    /*
     * Pointer to the end of object, where ENodeAllocator allocated enough space for Enode's children and
     * their use-vector indices.
     */
    ERef args[0];

    friend class EnodeAllocator;
    Enode(SymRef symbol, opensmt::span<ERef> children, ERef myRef, PTRef ptr);

public:
    Enode(Enode const &) = delete;

    CgId  getCid() const { return cid; }
    ERef getRoot() const { return root; }
    void setRoot(ERef r) { root = r; }

    ERef getEqNext () const {  return eq_next; }
    void setEqNext (ERef n) { eq_next = n; }
    int  getEqSize () const { return eq_size; }
    void setEqSize (int i) { eq_size = i; }

    PtAsgn getExpReason       () const { return exp_reason; }
    ERef   getExpParent       () const { return exp_parent; }
    ERef   getExpRoot         () const { return exp_root; }
    int    getExpTimeStamp    () const { return exp_time_stamp; }

    void setExpReason     (PtAsgn r)     { exp_reason = r; }
    void setExpParent     (ERef r)       { exp_parent = r; }
    void setExpRoot       (ERef r)       { exp_root   = r; }
    void setExpTimeStamp  (const int t)  { exp_time_stamp = t; }

    PTRef getTerm       ()        const { return pterm; }
    ELRef getForbid     ()        const { return forbid; }
    void  setForbid     (ELRef r)       { forbid = r; }
    void  setDistClasses( const dist_t& d) { dist_classes = d; }
    dist_t getDistClasses() const { return dist_classes; }

    uint32_t getSize() const { return argSize; }
    SymRef getSymbol() const { return symb; }
    ERef operator[](std::size_t i) const { return *(args + i); }
    ERef const * begin() const { return args; }
    ERef const * end() const { return args + argSize; }
    UseVectorIndex getIndex(uint32_t i) const { return UseVectorIndex{(args + argSize + i)->x}; }
    void setIndex(uint32_t i, UseVectorIndex index) { (args + argSize + i)->x = index.x; }
};

struct ERefHash {
    uint32_t operator () (const ERef& s) const {
        return (uint32_t)s.x; }
};

class EnodeAllocator : public RegionAllocator<uint32_t>
{
    enodeid_t n_enodes;
 public:

    EnodeAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_enodes(0) {}
    EnodeAllocator() : n_enodes(0) {}

    /* The children refs and corresponding use-vector indices are stored at the end of the object */
    static int enodeWord32Size(std::size_t argCount) { return (sizeof(Enode) + 2 * argCount * sizeof(ERef)) / sizeof(int32_t); }

    void moveTo(EnodeAllocator& to){
        RegionAllocator<uint32_t>::moveTo(to);
        to.n_enodes = n_enodes;
    }

    ERef alloc(SymRef symbol, opensmt::span<ERef> children, PTRef term) {
        static_assert(sizeof(SymRef) == sizeof(uint32_t), "Expected size of types does not match");
        static_assert(sizeof(ERef)   == sizeof(uint32_t), "Expected size of types does not match");

        uint32_t v = RegionAllocator<uint32_t>::alloc(enodeWord32Size(children.size()));
        // MB: The data structures used in the satisfiability checking algorithm (UseVector) requires at the moment that
        // the values of ERef cannot exceed 2^30. The benchmarks that we are dealing with at the moment are far below this limit,
        // but here is a dynamic check just in case.
        if (v >= (static_cast<uint32_t>(-1) >> 2)) { throw OutOfMemoryException(); }
        ERef eref{v};
        ++n_enodes;
        new (lea(eref)) Enode(symbol, children, eref, term);
        return eref;
    }

    ERef alloc(Enode&) = delete;

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Enode&       operator[](ERef r)         { return (Enode&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Enode& operator[](ERef r) const   { return (Enode&)RegionAllocator<uint32_t>::operator[](r.x); }
    Enode*       lea       (ERef r)         { return (Enode*)RegionAllocator<uint32_t>::lea(r.x); }
    const Enode* lea       (ERef r) const   { return (Enode*)RegionAllocator<uint32_t>::lea(r.x); }
    ERef         ael       (const Enode* t) { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); ERef rf; rf.x = r; return rf; }

    void free(ERef eid)
    {
        Enode& e = operator[](eid);
        RegionAllocator<uint32_t>::free(enodeWord32Size(e.getSize()));
    }

};


/**
 * Expl is a generalization of an explanation inequality that covers explicitly
 * the standard inequality consisting of a negated equality or inequality,
 * difference of two constants, and a boolean atom and its negation being distinct.
 */
struct Expl {
    enum class Type { std, cons, pol, undef } type;
    PtAsgn pta;
    PTRef pol_term;
    Expl() : type(Type::undef), pta(PtAsgn_Undef), pol_term(PTRef_Undef) {}
    Expl(Type type, PtAsgn pta, PTRef pol_term) : type(type), pta(pta), pol_term(pol_term) {}
};

#define ID_BITS 30
#define ID_MAX 2 << 30
class Elist
{
    struct {
        unsigned rlcd      : 1;
        unsigned dirty     : 1;
        unsigned id        : ID_BITS; } header;

    ELRef    relocation() const { return rel_e; }
    void     relocate(ELRef er) { header.rlcd = 1; rel_e = er; }
    void     setId(uint32_t id) { assert(id < (uint32_t)(ID_MAX)); header.id = id; }
    friend class ELAllocator;

public:
    bool     reloced()    const { return header.rlcd; }
    unsigned getId()      const { return header.id; }
    void     setDirty()         { header.dirty = true; }
    bool     isDirty()    const { return header.dirty; }
    Expl     reason;                   // Reason for this distinction
    union    { ERef e; ELRef rel_e; }; // Enode that differs from this, or the reference where I was relocated
    ELRef    link;                     // Link to the next element in the list

    Elist(ERef e_, const Expl &r) : reason(r), e(e_), link(ELRef_Undef) {
        header.rlcd = false;
        header.dirty = false;
    }
    Elist* Elist_new(ERef e_, const Expl &r) {
        assert(false);
        assert(sizeof(ELRef) == sizeof(uint32_t));
        size_t sz = sizeof(ELRef) + 2*sizeof(ERef);
        void* mem = malloc(sz);
        return new (mem) Elist(e_, r);
    }
};


class ELAllocator : public RegionAllocator<uint32_t>
{
    int free_ctr;
    static int elistWord32Size() {
        return sizeof(Elist)/sizeof(int32_t);
    }
public:
    vec<ELRef> elists;
    std::vector<vec<ERef> > referenced_by;
    ELAllocator() : free_ctr(0) {}
    ELAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), free_ctr(0) {}

    void addReference(ELRef ref, ERef referer) {
        int id = operator[] (ref).getId();
        referenced_by[id].push(referer);
    }

    void moveTo(ELAllocator& to) {
        RegionAllocator<uint32_t>::moveTo(to);
        elists.copyTo(to.elists);
        to.referenced_by.clear();
        for (const auto & referencers : referenced_by) {
            to.referenced_by.emplace_back();
            for (auto referencer : referencers)
                to.referenced_by.back().push(referencer);
        }
    }
    ELRef alloc(ERef e, const Expl& r, ERef owner) {
        assert(sizeof(ERef) == sizeof(uint32_t));
        uint32_t v = RegionAllocator<uint32_t>::alloc(elistWord32Size());
        ELRef elid;
        elid.x = v;
        new (lea(elid)) Elist(e, r);
        operator[] (elid).setId(elists.size());
#ifdef GC_DEBUG
        for (int i = 0; i < elists.size(); i++)
            assert(elists[i] != elid);
#endif
        assert(static_cast<int>(referenced_by.size()) == elists.size());
        elists.push(elid);
        referenced_by.emplace_back();
        referenced_by.back().push(owner);
        
        return elid;
    }

    ELRef alloc(const Elist& old) {
        uint32_t v = RegionAllocator<uint32_t>::alloc(elistWord32Size());
        ELRef elid;
        elid.x = v;
        new (lea(elid)) Elist(old.e, old.reason);
        operator[] (elid).setId(elists.size());
        elists.push(elid);
        return elid;
    }

    Elist&       operator[](ELRef r)         { return (Elist&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Elist& operator[](ELRef r) const   { return (Elist&)RegionAllocator<uint32_t>::operator[](r.x); }
    Elist*       lea       (ELRef r)         { return (Elist*)RegionAllocator<uint32_t>::lea(r.x); }
    const Elist* lea       (ELRef r) const   { return (Elist*)RegionAllocator<uint32_t>::lea(r.x); }
    ELRef        ael       (const Elist* t)  { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); ELRef rf; rf.x = r; return rf; }

    void free(ELRef r)
    {
        free_ctr++;
        RegionAllocator<uint32_t>::free(elistWord32Size());
        assert(!operator[](r).isDirty());
        (operator[](r)).setDirty();
    }

    void reloc(ELRef& elr, ELAllocator& to)
    {
        Elist& el = operator[](elr);

        if (el.reloced()) { elr = el.relocation(); return; }

        elr = to.alloc(el);
        to.referenced_by.emplace_back();
        assert(static_cast<unsigned int>(to.referenced_by.size()) == to[elr].getId()+1);

        // copy referers from old allocator to new
        vec<ERef>& referers = referenced_by[el.getId()];
        for (int i = 0; i < referers.size(); i++) {
            ERef er = referers[i];
            if (er != ERef_Undef)
                to.referenced_by.back().push(er);
        }
        el.relocate(elr);
    }

    void removeRef(ERef er, ELRef elr) {
        int i = 0;
        int id = operator[] (elr).getId();
        for (; i < referenced_by[id].size(); i++) {
            if (referenced_by[id][i] == er) {
                referenced_by[id][i] = ERef_Undef;
                break;
            }
        }
        assert(i < referenced_by[id].size());
#ifdef GC_DEBUG
        for (i++; i < referenced_by[id].size(); i++)
            assert(referenced_by[id][i] != er);
#endif
    }
};

#endif
