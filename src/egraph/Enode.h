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

class CgData {
    ERef        root;           // Root of the equivalence class
    ERef        next;           // Next node in the class
    int         size;           // Size of the eq class
    ERef        parent;         // Parent of the node (in congruence)
    ERef        same_car;       // Circular list of all the car-parents of the class
    ERef        same_cdr;       // Circular list of all the cdr-parents of the class
    int         parent_size;    // Size of the parent's congruence class
    ERef        cg_ptr;         // Congruence class representative (how is this different from root?)
    ELRef       forbid;         // List of unmergeable Enodes
    dist_t      dist_classes;   // The bit vector for distinction classes
    int         dist_index;     // ?

    // Move these to a term-specific storage
    PTRef       exp_reason;
    ERef        exp_parent;
    ERef        exp_root;
    int         exp_class_size;
    ERef        exp_highest_node;
    int         exp_time_stamp;

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
    ERef        er;     // Either my tref or reference to the relocated one
    ERef        car;
    ERef        cdr;
    bool        is_deduced;
    bool        has_polarity;
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
    bool  isDeduced     ()        const { return is_deduced; }
    void  setDeduced    ()              { assert(type() == et_term); is_deduced = true; }
    void  resetDeduced  ()              { is_deduced = false; }
    bool  hasPolarity   ()        const { return has_polarity; }
    SymRef getSymb      ()        const { assert(type() == et_symb); return symb; }
    PTRef getTerm       ()        const { assert(type() != et_symb && type() != et_list); return pterm; }
    ERef  getRoot       ()        const { if (type() == et_symb) return er; else return cgdata->root; }
    void  setRoot       (ERef r)        { assert(type() != et_symb); cgdata->root = r; }
    ELRef getForbid     ()        const { return cgdata->forbid; }
    ELRef& altForbid    ()              { return cgdata->forbid; }
    void  setForbid     (ELRef r)       { cgdata->forbid = r; }
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
    static int enodeWord32Size(bool has_cgdata){
        if (has_cgdata) return (sizeof(Enode) + sizeof(CgData))/sizeof(int32_t);
        else            return sizeof(Enode)/sizeof(int32_t); }

    Map<SigPair,ERef,SigHash,Equal<const SigPair&> >* sig_tab;

 public:

    EnodeAllocator(uint32_t start_cap, Map<SigPair,ERef,SigHash,Equal<const SigPair&> >* st) : RegionAllocator<uint32_t>(start_cap), sig_tab(st) {}
    EnodeAllocator() {}

    void moveTo(EnodeAllocator& to){
        RegionAllocator<uint32_t>::moveTo(to); }

    // For symbols
    ERef alloc(SymRef sym) {
        assert(sizeof(SymRef)     == sizeof(uint32_t));
        assert(sizeof(ERef)     == sizeof(uint32_t));
        uint32_t v = RegionAllocator<uint32_t>::alloc(enodeWord32Size(false));
        ERef eid;
        eid.x = v;
        Enode* tmp = new (lea(eid)) Enode(sym, eid);
        tmp->header.type = Enode::et_symb;
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
/*
  Enode ( const enodeid_t, SymRef ) :
      id(geid++);
    , header.type(ETYPE_SYM)
  //
  // Constructor for terms and lists
  //
  Enode ( const enodeid_t       // id
        , Enode *               // car
        , Enode *               // cdr
        );
  //
  // Constructor for defs -- what is a def?
  //
  Enode ( const enodeid_t       // id
        , Enode *               // def
        );
  //
  // Destructor
  //
  ~Enode ( );
  //
  // Check if a node is Enil
  //
  inline bool isEnil            ( ) const { return id == ENODE_ID_ENIL; }
  inline bool isList            ( ) const { return (properties & ETYPE_MASK) == ETYPE_LIST; }
  inline bool isTerm            ( ) const { return (properties & ETYPE_MASK) == ETYPE_TERM; }
  inline bool isSymb            ( ) const { return (properties & ETYPE_MASK) == ETYPE_SYMB; }
  inline bool isNumb            ( ) const { return (properties & ETYPE_MASK) == ETYPE_NUMB; }
  inline bool isDef             ( ) const { return (properties & ETYPE_MASK) == ETYPE_DEF; }

  inline void setEtype          ( const etype_t t )
  {
    assert( t == ETYPE_SYMB
         || t == ETYPE_NUMB
         || t == ETYPE_LIST
         || t == ETYPE_TERM
         || t == ETYPE_DEF );
    properties |= t;
  }

  inline void setArity            ( const unsigned a ) { assert( a <= ARITY_N ); properties |= (a << ARITY_SHIFT); }

  inline bool hasCongData         ( ) const { return cong_data != NULL; }
  void        allocCongData       ( );
  void        deallocCongData     ( );

  //
  // Getty and Setty methods
  //
  inline enodeid_t            getId      ( ) const { return id; }
  inline SymRef                 getTerm    ( ) const { return tr; }

  inline Enode *  getCar                 ( ) const { return car; }
  inline Enode *  getCdr                 ( ) const { return cdr; }
//  inline Enode *  getDef                 ( ) const { assert( isDef( ) ); assert( car ); return car; }

  inline Enode *  getNext                ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->next; }
  inline int      getSize                ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->size; }
  inline Enode *  getParent              ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->parent; }
  inline Enode *  getSameCar             ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->same_car; }
  inline Enode *  getSameCdr             ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->same_cdr; }
  inline int      getParentSize          ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->parent_size; }
  inline Enode *  getCgPtr               ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->cg_ptr; }
  inline Elist *  getForbid              ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->forbid; }
  inline dist_t   getDistClasses         ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->dist_classes; }

  Enode *         getRoot                ( ) const;
  enodeid_t       getCid                 ( ) const;
  Enode *         getConstant            ( ) const;
                  
  inline Enode *  getExpReason           ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_reason; }
  inline Enode *  getExpParent           ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_parent; }
  inline Enode *  getExpRoot             ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_root; }
  inline int      getExpClassSize        ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_class_size; }
  inline Enode *  getExpHighestNode      ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_highest_node; }
  // inline Reason * getExpReason           ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_reason; }
  inline int      getExpTimeStamp        ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_time_stamp; }

  inline lbool    getPolarity            ( ) const { assert( isTerm( ) && atom_data ); return atom_data->polarity; }
  inline bool	  hasPolarity            ( ) const { assert( isTerm( ) && atom_data ); return atom_data->has_polarity; }
  inline lbool    getDeduced             ( ) const { assert( isTerm( ) && atom_data ); return atom_data->deduced; }
  inline bool     isDeduced              ( ) const { assert( isTerm( ) && atom_data ); return atom_data->is_deduced; }
  inline lbool    getDecPolarity         ( )       { assert( isAtom( ) && atom_data ); return atom_data->dec_polarity; }
  inline int      getWeightInc           ( )       { assert( isAtom( ) && atom_data ); return atom_data->weight_inc; }
  inline int      getDedIndex            ( ) const { assert( isTerm( ) && atom_data ); return atom_data->ded_index; }
  inline int      getDistIndex           ( ) const { assert( isTerm( ) && atom_data ); return atom_data->dist_index; }

  inline Enode *  getCb                  ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->cb; }
  inline Enode *  getRef                 ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->root; }
  inline int      getWidth               ( ) const { assert( isTerm( ) || isSymb( ) || isNumb( ) ); return (properties & WIDTH_MASK); }

  inline void     setWidth               ( const uint32_t w )
  {
    assert( isTerm( ) );
    assert( w < MAX_WIDTH );
    // Reset width
    properties &= ~WIDTH_MASK;
    properties |= w;
    assert( getWidth( ) == static_cast<int>( w ) );
  }

  inline void    setRoot                ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->root = e; }
  inline void    setCid                 ( const enodeid_t c ){ assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->cid = c; } // Congruence id?
  inline void    setDef                 ( Enode * e )        { assert( e ); assert( isDef( ) ); car = e; }
  inline void    setNext                ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->next = e; }
  inline void    setSize                ( const int s )      { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->size = s; }
  inline void    setParent              ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->parent = e; }
  inline void    setSameCar             ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->same_car = e; }
  inline void    setSameCdr             ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->same_cdr = e; }
  inline void    setParentSize          ( const int s )      { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->parent_size = s; }
  inline void    setCgPtr               ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->cg_ptr = e; }
  inline void    setForbid              ( Elist * l )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->forbid = l; }
  inline void    setDistClasses         ( const dist_t & d ) { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->dist_classes = d; }

  inline void    setConstant            ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); assert( e == NULL || e->isConstant( ) ); cong_data->term_data->constant = e; }
  inline void    setExpReason           ( Enode * r )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_reason = r; }
  inline void    setExpParent           ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_parent = e; }
  inline void    setExpRoot             ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_root = e; }
  inline void    setExpClassSize        ( const int s )          { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_class_size = s; }
  inline void    setExpHighestNode      ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_highest_node = e; }
  inline void    setExpTimeStamp        ( const int t )          { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_time_stamp = t; }
  inline void    setPolarity            ( const lbool p )        { assert( isTerm( ) && atom_data ); assert( !atom_data->has_polarity ); atom_data->polarity = p; atom_data->has_polarity = true; }
  inline void    resetPolarity          ( )			 { assert( isTerm( ) && atom_data ); assert( atom_data->has_polarity ); atom_data->has_polarity = false; }
  inline void    setDeduced             ( const lbool d, int i ) { assert( isTerm( ) && atom_data ); assert( !atom_data->is_deduced ); atom_data->deduced = d; atom_data->ded_index = i; atom_data->is_deduced = true; }
  inline void    setDeduced             ( const bool s, int i )  { setDeduced( s ? l_False : l_True, i ); }
  inline void    resetDeduced           ( )			 { assert( isTerm( ) && atom_data ); assert( atom_data->is_deduced ); atom_data->is_deduced = false; }
  inline void    setDecPolarity         ( const lbool s )        { assert( isAtom( ) && atom_data ); atom_data->dec_polarity = s; }
  inline void    setWeightInc           ( const int w )          { assert( isAtom( ) && atom_data ); atom_data->weight_inc = w; }
  inline void    setDistIndex           ( const int d )	         { assert( isTerm( ) && atom_data ); atom_data->dist_index = d; }

  inline void    setCb                  ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->cb = e; }

  //
  // Congruence closure related routines
  //
  void           addParent              ( Enode * );   // Adds a parent to this node. Useful for congruence closure
  void           addParentTail          ( Enode * );   // Adds a parent to the tail of this node. Useful for congruence closure
  void           removeParent           ( Enode * );   // Remove a parent of this node
  //
  // Shortcuts for retrieving a term's arguments
  //
  inline Enode * get1st                 ( ) const;     // Get first argument in constant time (constant?)
  inline Enode * get2nd                 ( ) const;     // Get second argument in constant time
  inline Enode * get3rd                 ( ) const;     // Get third argument in constant time

  bool           addToCongruence        ( ) const;
  unsigned       sizeInMem              ( ) const;

  void           print                  ( ostream & ); // Prints the enode
  string         stripName              ( string );
  void           printSig               ( ostream & ); // Prints the enode signature

#ifdef BUILD_64
  inline enodeid_pair_t          getSig    ( ) const { return encode( car->getRoot( )->getCid( ), cdr->getRoot( )->getCid( ) ); }
#else
  inline const Pair( enodeid_t ) getSig    ( ) const { return make_pair( car->getRoot( )->getCid( ), cdr->getRoot( )->getCid( ) ); }
#endif
  inline enodeid_t               getSigCar ( ) const { return car->getRoot( )->getCid( ); }
  inline enodeid_t               getSigCdr ( ) const { return cdr->getRoot( )->getCid( ); }

#ifdef PRODUCE_PROOF
  inline const ipartitions_t & getIPartitions ( ) const                   { return ipartitions; }
  inline void                  setIPartitions ( const ipartitions_t & p ) { assert( ipartitions == 0 ); ipartitions = p; }
  inline void                  addIPartitions ( const ipartitions_t & p ) { assert( p != 0 ); ipartitions |= p; }
  // inline void                  oveIPartitions ( const ipartitions_t & p ) { assert( p != 0 ); ipartitions = p; }
#endif

  inline friend ostream & operator<<( ostream & os, Enode * e )    { assert( e ); e->print( os ); return os; }

  struct idLessThan
  {
    inline bool operator( )( Enode * x, Enode * y ) const
    {
      const Enode *x_car = x->getCar();
      const Enode *y_car = y->getCar();
      const enodeid_t x_car_id = x_car->getId();
      const enodeid_t y_car_id = y_car->getId();

      return (x_car_id < y_car_id)
	  || (x_car_id == y_car_id && x->getCdr( )->getId( ) < y->getCdr( )->getId( ) );
    }
  };

  struct cidLessThan
  {
    inline bool operator( )( Enode * x, Enode * y ) const
    {
      if ( x == y ) return false;
      if ( x->isEnil( ) ) return true;
      if ( y->isEnil( ) ) return false;
      return (x->getCar( )->getCid( ) <  y->getCar( )->getCid( ))
          || (x->getCar( )->getCid( ) == y->getCar( )->getCid( ) && x->getCdr( )->getCid( ) < y->getCdr( )->getCid( ) );
    }
  };

private:
  //
  // Standard informations for terms
  //
  const enodeid_t   id;          // Node unique identifier
  uint32_t          properties;  // Contains all the properties of this node (see EnodeTypes.h for bitfields definition)
  Enode *           car;         // For car / defs
  Enode *           cdr;         // For cdr
  union {
  CongData *        cong_data;   // For terms and lists that go in the congruence
  SymbData *        symb_data;   // For symbols/numbers
  };
  AtomData *        atom_data;   // For atom terms only
#ifdef PRODUCE_PROOF
  ipartitions_t     ipartitions; // Partitions for interpolation
#endif

  inline bool       hasSymbolId    ( const enodeid_t id ) const { assert( isTerm( ) ); return car->getId( ) == id; }
};


inline Enode * Enode::getRoot ( ) const
{
  assert( !isDef( ) );
  if ( (isTerm( ) || isList( )) && cong_data != NULL )
    return cong_data->root;
  return const_cast<Enode *>(this);
}

inline enodeid_t Enode::getCid ( ) const
{
  assert( !isDef( ) );
  if ( (isTerm( ) || isList( )) && cong_data )
    return cong_data->cid;
  return id;
}


inline Enode * Enode::get1st ( ) const
{
  assert( isTerm( ) );
  assert( getArity( ) > 0 );
  return getCdr( )->getCar( );
}

inline Enode * Enode::get2nd ( ) const
{
  assert( isTerm( ) );
  assert( getArity( ) > 1 );
  return getCdr( )->getCdr( )->getCar( );
}

inline Enode * Enode::get3rd ( ) const
{
  assert( isTerm( ) );
  assert( getArity( ) > 2 );
  return getCdr( )->getCdr( )->getCdr( )->getCar( );
}

inline unsigned Enode::sizeInMem( ) const
{
  assert(value == NULL);
  unsigned size = sizeof( Enode );
  if ( isSymb( ) )
  {
    assert( symb_data );
    assert( symb_data->name );
    size += sizeof( SymbData ) + strlen( symb_data->name );
  }
  if ( isNumb( ) )
  {
    assert( symb_data );
    assert( symb_data->name );
    assert( symb_data->value );
    size += sizeof( SymbData ) + strlen( symb_data->name ) + sizeof( Real );
  }
  if ( atom_data ) size += sizeof( AtomData );
  if ( cong_data )
  {
    size += sizeof( CongData );
    if ( cong_data->term_data ) size += sizeof( TermData );
  }
#ifdef PRODUCE_PROOF
  size += ipartitions.get_mpz_t()->_mp_alloc * sizeof(ipartitions.get_mpz_t()->_mp_d[0]);
#endif
  return size;
}

inline void Enode::allocCongData( )
{
  assert( isTerm( ) || isList( ) );
  assert( cong_data == NULL );
  cong_data = new CongData( id, const_cast<Enode *>(this) );
  if ( isTerm( ) )
    cong_data->term_data = new TermData( const_cast<Enode *>(this) );
}

inline void Enode::deallocCongData( )
{
  assert( isTerm( ) || isList( ) );
  assert( cong_data != NULL );
  if ( isTerm( ) )
  {
    assert( cong_data->term_data != NULL );
    delete cong_data->term_data;
    cong_data->term_data = NULL;
  }
  delete cong_data;
  cong_data = NULL;
}
*/
#endif
