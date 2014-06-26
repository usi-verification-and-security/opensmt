/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef ENODE_H
#define ENODE_H

#include "Vec.h"
#include "Alloc.h"

#include "symbols/Symbol.h"
#include "pterms/Pterm.h"

//#include "Global.h"
//#include "EnodeTypes.h"
//#include "Otl.h"
#include "sorts/Sort.h"
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

#ifdef CUSTOM_EL_ALLOC
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
#else
class Elist
{
public:
    Elist  *link;              // Link to the next element in the list
    ERef   e;                  // Enode that differs from this
    PtAsgn reason;             // Reason for this distinction
    Elist(ERef e_, PtAsgn r_) : link(NULL), e(e_), reason(r_) {}
};
#endif

class CgData {
    ERef        root;           // Root of the equivalence class
    ERef        next;           // Next node in the class
    int         size;           // Size of the eq class
    ERef        parent;         // Parent of the node (in congruence)
    ERef        same_car;       // Circular list of all the car-parents of the class
    ERef        same_cdr;       // Circular list of all the cdr-parents of the class
    int         parent_size;    // Size of the parent's congruence class
    ERef        cg_ptr;         // Congruence class representative (how is this different from root?)
#ifdef CUSTOM_EL_ALLOC
    ELRef       forbid;         // List of unmergeable Enodes
#else
    Elist*      forbid;         // List of unmergeable Enodes
#endif
    dist_t      dist_classes;   // The bit vector for distinction classes
    int         dist_index;     // ?

    // Move these to a term-specific storage
    PTRef       exp_reason;
    ERef        exp_parent;
    ERef        exp_root;
    int         exp_class_size;
    ERef        exp_highest_node;
    int         exp_time_stamp;

    PTRef       constant;

    friend class Enode;
};



class EnodeAllocator;

typedef uint32_t CgId;

class Enode
{
    static uint32_t cgid_ctr;

    struct {
        unsigned type       : 2;
        unsigned reloced    : 1;
        unsigned unused     : 29; } header;

    SymRef      symb;     // The symbol (if this is a symbol node) -- not sure this is necessary?
    PTRef       pterm;  // The proper term (if this is a term node)
    uint32_t    id;
    ERef        er;     // Either my eref or reference to the relocated one
    ERef        car;
    ERef        cdr;
    lbool       deduced;
//    bool        has_polarity;
    cgId        cid;            // The congruence id of the enode (defined also for symbols)

    // This is a trick to enable congruence data on only Enodes it is needed
    CgData      cgdata[0];


    friend class EnodeAllocator;
    friend class EnodeStore;

public:
    static ERef ERef_Nil;

    enum en_type { et_symb, et_list, et_term };

    // Constructor for symbols
    Enode(SymRef, ERef);

    // Constructor for term and list nodes
    Enode(ERef car_, ERef cdr_, en_type t, EnodeAllocator& ea, ERef er, Map<SigPair,ERef,SigHash,Equal<const SigPair&> >& sig_tab);

//    Enode* Enode_new(en_type t, SymRef tr) {
//        assert(sizeof(SymRef) == sizeof(uint32_t));
//        size_t sz = sizeof(header) + sizeof(SymRef) + sizeof(uint32_t);
//        if (t != et_symb) sz += sizeof(CgData);
//        void* mem = malloc(sz);
//
//        if (t == et_term || t == et_list) {
//            Enode* en = new (mem) Enode(tr);
//            new (en->cgdata) CgData();
//        }
//        return new (mem) Enode(tr);
//
//    }

    en_type type        ()        const { return (en_type)header.type; }

    void relocate       (ERef e)        { header.reloced = 1; er = e; }
    bool reloced        ()        const { return header.reloced; }
    ERef relocation     ()        const { return er; }

    uint32_t getId      ()        const { return id; }

    bool  isList        ()        const { return (en_type)header.type == et_list; }
    bool  isTerm        ()        const { return (en_type)header.type == et_term; }
    bool  isSymb        ()        const { return (en_type)header.type == et_symb; }
    uint32_t getArity   ()        const { return 2; } // FIXME
    ERef  getCar        ()        const { assert(type() != et_symb); return car; }
    ERef  getCdr        ()        const { assert(type() != et_symb); return cdr; }
    bool  isDeduced     ()        const { return deduced != l_Undef; }
    void  setDeduced    (lbool v)       { assert(type() == et_term); deduced = v; }
    lbool getDeduced    ()        const { return deduced; }
    void  resetDeduced  ()              { deduced = l_Undef; }
//    bool  hasPolarity   ()        const { return has_polarity; }
    SymRef getSymb      ()        const { assert(type() == et_symb); return symb; }
    PTRef getTerm       ()        const { assert(type() != et_symb && type() != et_list); return pterm; }
    ERef  getRoot       ()        const { if (type() == et_symb) return er; else return cgdata->root; }
    void  setRoot       (ERef r)        { assert(type() != et_symb); cgdata->root = r; }
#ifdef CUSTOM_EL_ALLOC
    ELRef getForbid     ()        const { return cgdata->forbid; }
    ELRef& altForbid    ()              { return cgdata->forbid; }
    void  setForbid     (ELRef r)       { cgdata->forbid = r; }
#else
    Elist* getForbid    ()        const { return cgdata->forbid; }
    Elist& altForbid    ()              { return *(cgdata->forbid); }
    void  setForbid     (Elist* r)      { cgdata->forbid = r; }
#endif
    int   getDistIndex  ()        const { return cgdata->dist_index; }
    void  setDistIndex  (int i)         { cgdata->dist_index = i; }
    ERef  getCgPtr      ()        const { return cgdata->cg_ptr; }
    void  setCgPtr      (ERef e)        { cgdata->cg_ptr = e; }
    CgId  getCid        ()        const { return cid; }
    void  setCid        (CgId id)       { cid = id; }

    ERef  getParent     ()        const { return cgdata->parent; }
    void  setParent     (ERef e)        { cgdata->parent = e; }
    int   getParentSize ()        const { return cgdata->parent_size; }
    void  setParentSize (int i)         { cgdata->parent_size = i; }
    ERef  getSameCdr    ()        const { return cgdata->same_cdr; }
    void  setSameCdr    (ERef e)        { cgdata->same_cdr = e; }
    ERef  getSameCar    ()        const { return cgdata->same_car; }
    void  setSameCar    (ERef e)        { cgdata->same_car = e; }

    ERef  getNext       ()        const { return cgdata->next; }
    void  setNext       (ERef n)        { cgdata->next = n; }
    int   getSize       ()        const { return cgdata->size; }
    void  setSize       (int i)         { cgdata->size = i; }

    void  setDistClasses( const dist_t& d) { cgdata->dist_classes = d; }

    inline dist_t getDistClasses() const { return cgdata->dist_classes; }

    PTRef getExpReason       () const { assert( isTerm() ); return cgdata->exp_reason; }
    ERef  getExpParent       () const { assert( isTerm() ); return cgdata->exp_parent; }
    ERef  getExpRoot         () const { assert( isTerm() ); return cgdata->exp_root; }
    int   getExpClassSize    () const { assert( isTerm() ); return cgdata->exp_class_size; }
    ERef  getExpHighestNode  () const { assert( isTerm() ); return cgdata->exp_highest_node; }
    int   getExpTimeStamp    () const { assert( isTerm() ); return cgdata->exp_time_stamp; }

    void setExpReason           ( PTRef r )           { assert( isTerm() ); cgdata->exp_reason = r; }
    void setExpParent           ( ERef e )            { assert( isTerm() ); cgdata->exp_parent = e; }
    void setExpRoot             ( ERef e )            { assert( isTerm() ); cgdata->exp_root   = e; }
    void setExpClassSize        ( const int s )       { assert( isTerm() ); cgdata->exp_class_size   = s; }
    void setExpHighestNode      ( ERef e )            { assert( isTerm() ); cgdata->exp_highest_node = e; }
    void setExpTimeStamp        ( const int t )       { assert( isTerm() ); cgdata->exp_time_stamp   = t; }
//    friend class CgData;

    void setConstant            (PTRef tr)            { assert(isTerm()); cgdata->constant = tr; }
    PTRef getConstant           ()                    { assert(isTerm()); return cgdata->constant; }
    void clearConstant          ()                    { assert(isTerm()); cgdata->constant = PTRef_Undef; }
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
    static int enodeWord32Size(bool has_cgdata){
        if (has_cgdata) return (sizeof(Enode) + sizeof(CgData))/sizeof(int32_t);
        else            return sizeof(Enode)/sizeof(int32_t); }

    Map<SigPair,ERef,SigHash,Equal<const SigPair&> >* sig_tab;

 public:

    EnodeAllocator(uint32_t start_cap, Map<SigPair,ERef,SigHash,Equal<const SigPair&> >* st) : RegionAllocator<uint32_t>(start_cap), n_enodes(0), sig_tab(st) {}
    EnodeAllocator() : n_enodes(0) {}

    void moveTo(EnodeAllocator& to){
        RegionAllocator<uint32_t>::moveTo(to);
        to.n_enodes = n_enodes;
    }

    // For symbols
    ERef alloc(SymRef sym) {
        assert(sizeof(SymRef)     == sizeof(uint32_t));
        assert(sizeof(ERef)     == sizeof(uint32_t));
        uint32_t v = RegionAllocator<uint32_t>::alloc(enodeWord32Size(false));
        ERef eid;
        eid.x = v;
        Enode* tmp = new (lea(eid)) Enode(sym, eid);
        tmp->header.type = Enode::et_symb;
        tmp->id = n_enodes++;
        return eid;
    }

    // For terms and lists
    ERef alloc(ERef car, ERef cdr, Enode::en_type t, PTRef ptr)
    {
        assert(sizeof(SymRef)     == sizeof(uint32_t));
        assert(sizeof(ERef)     == sizeof(uint32_t));

        bool has_cgdata = (t == Enode::et_list) || (t == Enode::et_term);
        uint32_t v = RegionAllocator<uint32_t>::alloc(enodeWord32Size(has_cgdata));
        ERef eid;
        eid.x = v;
        Enode* tmp = new (lea(eid)) Enode(car, cdr, t, *this, eid, *sig_tab);
        tmp->header.type = t;
        tmp->pterm = ptr;
        tmp->id = n_enodes++;
        return eid;
    }

    ERef alloc(Enode&) {
        assert(false);
        return ERef_Undef;
    }

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
        if ((e.type() == Enode::et_list) || (e.type() == Enode::et_term))
            RegionAllocator<uint32_t>::free(enodeWord32Size(true));
        else
            RegionAllocator<uint32_t>::free(enodeWord32Size(false));

    }

    void reloc(ERef& er, EnodeAllocator& to)
    {
        Enode& e = operator[](er);

        if (e.reloced()) { er = e.relocation(); return; }

        er = to.alloc(e);
        e.relocate(er);
    }

};


#ifdef CUSTOM_EL_ALLOC
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

#endif
