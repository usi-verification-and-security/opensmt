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
#include "Global.h"

#include "CgTypes.h"
#include "SigMap.h"

//typedef RegionAllocator<uint32_t>::Ref ERef;

struct ERef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator<  (const ERef& a1, const ERef& a2) {return a1.x < a2.x;  }
    inline friend bool operator== (const ERef& a1, const ERef& a2) {return a1.x == a2.x; }
    inline friend bool operator!= (const ERef& a1, const ERef& a2) {return a1.x != a2.x; }
};
static struct ERef ERef_Undef = {INT32_MAX};

//
// Data structure used to store forbid lists
//

struct ELRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const ELRef& a1, const ELRef& a2) {return a1.x == a2.x; }
    inline friend bool operator!= (const ELRef& a1, const ELRef& a2) {return a1.x != a2.x; }
//    struct ELRef operator() (uint32_t v) { x = v; return *this;}
//    explicit ELRef(uint32_t v) { x = v; }
};

// FIXME this is uninitialized right now.
static struct ELRef ELRef_Undef = {INT32_MAX};

class Extra {
    struct {
        ERef        car;
        ERef        cdr;
        ERef        next;           // Next node in the class
        int         size;           // Size of the eq class
        ERef        parent;         // Parent of the node (in congruence)
        ERef        same_car;       // Circular list of all the car-parents of the class
        ERef        same_cdr;       // Circular list of all the cdr-parents of the class
        int         parent_size;    // Size of the parent's congruence class
        ERef        cg_ptr;         // Congruence class representative (how is this different from root?)
    } lst;
    struct {
        PTRef       pterm;          // The corresponding pterm
        ELRef       forbid;         // List of unmergeable Enodes
        dist_t      dist_classes;   // The bit vector for distinction classes
        int         dist_index;     // My distinction index
        // fields related to explanation
        PtAsgn      exp_reason;
        ERef        exp_parent;
        ERef        exp_root;
        int         exp_time_stamp;
    } trm;
    friend class Enode;
    friend class EnodeAllocator;
};

class EnodeAllocator;

typedef uint32_t CgId;

class Enode
{
protected:
    static uint32_t cgid_ctr;

    struct {
        unsigned type      : 2;
        enodeid_t id       : 30; } header;

    static_assert(sizeof(SymRef) == sizeof(ERef), "Expected size of types does not match");
    union {
        SymRef symb;
        ERef   root;
    };

    ERef        er;             // Either my eref or reference to the relocated one
    cgId        cid;            // The congruence id of the enode (defined also for symbols)
    // Must be last field!
    Extra       ex[0];          // Enode specific data

    friend class EnodeAllocator;
    friend class EnodeStore;

public:
    static ERef ERef_Nil;
    enum en_type { et_symb, et_list, et_term };

    // For symbols
    Enode(SymRef symb_, ERef er_, enodeid_t id_)
        : header  ({et_symb, id_})
        , symb     (symb_)
        , er      (er_)
        , cid     (cgid_ctr++) {}

    // For lists and terms
    Enode(ERef car_, ERef cdr_, EnodeAllocator& ea, ERef er_, enodeid_t id_, PTRef ptr = PTRef_Undef);
    // Defined for all Enodes

    en_type type        ()        const { return (en_type)header.type; }
    uint32_t getId      ()        const { return header.id; }

    bool  isList        ()        const { return (en_type)header.type == et_list; }
    bool  isTerm        ()        const { return (en_type)header.type == et_term; }
    bool  isSymb        ()        const { return (en_type)header.type == et_symb; }

    CgId  getCid        ()        const { return cid; }
    void  setCid        (CgId id)       { cid = id; }

    // Defined for symbol enodes
    SymRef getSymb()             const { assert(type() == et_symb); return symb; }

    // Defined for list and term Enodes
private:
    void setCar(ERef er)               { assert(type() != et_symb); ex->lst.car = er; }
    void setCdr(ERef er)               { assert(type() != et_symb); ex->lst.cdr = er; }
public:
    ERef getCar()                const { assert(type() != et_symb); return ex->lst.car; }
    ERef getCdr()                const { assert(type() != et_symb); return ex->lst.cdr; }
    ERef getRoot()               const { if (isSymb()) return er; else return root; }
    void setRoot       (ERef r)        { assert(type() != et_symb); root = r; }
    ERef getCgPtr      ()        const { assert(type() != et_symb); return ex->lst.cg_ptr; }
    void setCgPtr      (ERef e)        { assert(type() != et_symb); ex->lst.cg_ptr = e; }

    ERef getParent     ()        const { assert(type() != et_symb); return ex->lst.parent; }
    void setParent     (ERef e)        { assert(type() != et_symb); ex->lst.parent = e; }
    int  getParentSize ()        const { assert(type() != et_symb); return ex->lst.parent_size; }
    void setParentSize (int i)         { assert(type() != et_symb); ex->lst.parent_size = i; }
    ERef getSameCdr    ()        const { assert(type() != et_symb); return ex->lst.same_cdr; }
    void setSameCdr    (ERef e)        { assert(type() != et_symb); ex->lst.same_cdr = e; }
    ERef getSameCar    ()        const { assert(type() != et_symb); return ex->lst.same_car; }
    void setSameCar    (ERef e)        { assert(type() != et_symb); ex->lst.same_car = e; }

    ERef getNext       ()        const { assert(type() != et_symb); return ex->lst.next; }
    void setNext       (ERef n)        { assert(type() != et_symb); ex->lst.next = n; }
    int  getSize       ()        const { assert(type() != et_symb); return ex->lst.size; }
    void setSize       (int i)         { assert(type() != et_symb); ex->lst.size = i; }
    ERef getERef       ()        const { return er; }

    PtAsgn getExpReason       () const { assert(type() == et_term); return ex->trm.exp_reason; }
    ERef   getExpParent       () const { assert(type() == et_term); return ex->trm.exp_parent; }
    ERef   getExpRoot         () const { assert(type() == et_term); return ex->trm.exp_root; }
    int    getExpTimeStamp    () const { assert(type() == et_term); return ex->trm.exp_time_stamp; }

    void setExpReason     (PtAsgn r)     { assert(type() == et_term); ex->trm.exp_reason = r; }
    void setExpParent     (ERef r)       { assert(type() == et_term); ex->trm.exp_parent = r; }
    void setExpRoot       (ERef r)       { assert(type() == et_term); ex->trm.exp_root   = r; }
    void setExpTimeStamp  (const int t)  { assert(type() == et_term); ex->trm.exp_time_stamp   = t; }

private:
    void  setPterm      (PTRef tr)      { assert(isTerm()); ex->trm.pterm = tr; }
public:
    PTRef getTerm       ()        const { assert(isTerm()); return ex->trm.pterm; }
//    ELRef getForbid     ()        const { assert(isTerm()); return ex->trm.forbid; }
    ELRef getForbid     ()        const { assert(!isSymb()); if (isList()) return ELRef_Undef; else return ex->trm.forbid; }
    ELRef& altForbid    ()              { assert(isTerm()); return ex->trm.forbid; }
    void  setForbid     (ELRef r)       { assert(isTerm()); ex->trm.forbid = r; }
//    int   getDistIndex  ()        const { assert(isTerm()); return ex->trm.dist_index; }
    int   getDistIndex  ()        const { assert(!isSymb()); if (isList()) return 0; else return ex->trm.dist_index; }
    void  setDistIndex  (int i)         { assert(isTerm()); ex->trm.dist_index = i; }
//    void  setDistClasses( const dist_t& d) { assert(isTerm()); ex->trm.dist_classes = d; }
    void  setDistClasses( const dist_t& d) { assert(!isSymb()); if (isList()) assert(d == 0); else ex->trm.dist_classes = d; }

//    inline dist_t getDistClasses() const { assert(isTerm()); return ex->trm.dist_classes; }
    inline dist_t getDistClasses() const { assert(!isSymb()); if (isTerm()) return ex->trm.dist_classes; else return 0; }
};

struct ERefHash {
    uint32_t operator () (const ERef& s) const {
        return (uint32_t)s.x; }
};

struct ERef_vecHash {
    uint32_t operator () (const vec<ERef>& s) const {
        int m = 0; for (int i = 0; i < s.size(); i++) m += s[i].x;
        return m; }
};

struct ERef_vecEq {
    bool operator () (const vec<ERef>& s1, const vec<ERef>& s2) const {
        if (s1.size() != s2.size()) return false;
        for (int i = 0; i < s1.size(); i++)
            if (s1[i] != s2[i]) return false;
        return true; }
};


class EnodeAllocator : public RegionAllocator<uint32_t>
{
    enodeid_t n_enodes;
 public:

    EnodeAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_enodes(0) {}
    EnodeAllocator() : n_enodes(0) {}

    static int symEnodeWord32Size()  { return sizeof(Enode) / sizeof(int32_t); }
    static int listEnodeWord32Size() { return (sizeof(Enode) + sizeof(Extra::lst)) / sizeof(int32_t); }
    static int termEnodeWord32Size() { return (sizeof(Enode) + sizeof(Extra)) / sizeof(int32_t); }

    void moveTo(EnodeAllocator& to){
        RegionAllocator<uint32_t>::moveTo(to);
        to.n_enodes = n_enodes;
    }

    // For symbols
    ERef alloc(SymRef sym) {
        static_assert(sizeof(SymRef) == sizeof(uint32_t), "Expected size of types does not match");
        static_assert(sizeof(ERef)   == sizeof(uint32_t), "Expected size of types does not match");
        uint32_t v = RegionAllocator<uint32_t>::alloc(symEnodeWord32Size());
        ERef eid;
        eid.x = v;
        Enode* tmp = new (lea(eid)) Enode(sym, eid, n_enodes++);
        tmp->header.id = n_enodes++;
        return eid;
    }

    // For terms and lists
    ERef alloc(ERef car, ERef cdr, Enode::en_type t, PTRef ptr)
    {
        static_assert(sizeof(SymRef) == sizeof(uint32_t), "Expected size of types does not match");
        static_assert(sizeof(ERef)   == sizeof(uint32_t), "Expected size of types does not match");

        assert(t == Enode::et_list || t == Enode::et_term);
        uint32_t v = RegionAllocator<uint32_t>::alloc(t == Enode::et_list ? listEnodeWord32Size() : termEnodeWord32Size());
        ERef eid;
        eid.x = v;
        assert(t != Enode::et_list || ptr == PTRef_Undef);
        Enode* tmp = new (lea(eid)) Enode(car, cdr, *this, eid, n_enodes++, ptr);
        return eid;
    }

    ERef alloc(Enode&) = delete;

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Enode&       operator[](ERef r)         { return (Enode&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Enode& operator[](ERef r) const   { return (Enode&)RegionAllocator<uint32_t>::operator[](r.x); }
    Enode*       lea       (ERef r)         { return (Enode*)RegionAllocator<uint32_t>::lea(r.x); }
    const Enode* lea       (ERef r) const   { return (Enode*)RegionAllocator<uint32_t>::lea(r.x); }
    const Enode& dbg       (int  r) const   { return (Enode&)RegionAllocator<uint32_t>::operator[](r); }
    ERef         ael       (const Enode* t) { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); ERef rf; rf.x = r; return rf; }

    void free(ERef eid)
    {
        Enode& e = operator[](eid);
        if ((e.type() == Enode::et_list))
            RegionAllocator<uint32_t>::free(listEnodeWord32Size());
        else if (e.type() == Enode::et_term)
            RegionAllocator<uint32_t>::free(termEnodeWord32Size());
        else
            RegionAllocator<uint32_t>::free(symEnodeWord32Size());

    }

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
    PtAsgn   reason;                   // Reason for this distinction
    union    { ERef e; ELRef rel_e; }; // Enode that differs from this, or the reference where I was relocated
    ELRef    link;                     // Link to the next element in the list

    Elist(ERef e_, PtAsgn r) : reason(r), e(e_), link(ELRef_Undef) {
        header.rlcd = false;
        header.dirty = false;
    }
    Elist* Elist_new(ERef e_, PtAsgn r) {
        assert(false);
        assert(sizeof(ELRef) == sizeof(uint32_t));
        size_t sz = sizeof(ELRef) + 2*sizeof(ERef);
        void* mem = malloc(sz);
//        return new (mem) Elist(e_, r, owner);
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
    vec<vec<ERef> > referenced_by;
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
        for (int i = 0; i < referenced_by.size(); i++) {
            to.referenced_by.push();
            for (int j = 0; j < referenced_by[i].size(); j++)
                to.referenced_by.last().push(referenced_by[i][j]);
        }
    }
    ELRef alloc(ERef e, PtAsgn r, ERef owner) {
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
        assert(referenced_by.size() == elists.size());
        elists.push(elid);
        referenced_by.push();
        referenced_by.last().push(owner);
        
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
        to.referenced_by.push();
        assert(to.referenced_by.size() == to[elr].getId()+1);

        // copy referers from old allocator to new
        vec<ERef>& referers = referenced_by[el.getId()];
        for (int i = 0; i < referers.size(); i++) {
            ERef er = referers[i];
            if (er != ERef_Undef)
                to.referenced_by.last().push(er);
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
