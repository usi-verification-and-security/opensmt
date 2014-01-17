#include "logics/Logic.h"
#include "minisat/mtl/Vec.h"
#include "cnfizers/Cnfizer.h"

#ifndef Simplifiers_TopLevelPropagate_h
#define Simplifiers_TopLevelPropagate_h

struct SERef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator<  (const SERef& a1, const SERef& a2) {return a1.x < a2.x;  }
    inline friend bool operator== (const SERef& a1, const SERef& a2) {return a1.x == a2.x; }
    inline friend bool operator!= (const SERef& a1, const SERef& a2) {return a1.x != a2.x; }
};
static struct SERef SERef_Undef = {INT32_MAX};

class SEAllocator;
typedef uint32_t CgId;

class SEnode
{
    class SCgData {
      public:
        SERef        root;           // Root of the equivalence class
        SERef        next;           // Next node in the class
        int         size;           // Size of the eq class
        SERef        parent;         // Parent of the node (in congruence)
        SERef        same_car;       // Circular list of all the car-parents of the class
        SERef        same_cdr;       // Circular list of all the cdr-parents of the class
        int         parent_size;    // Size of the parent's congruence class
        SERef        cg_ptr;         // Congruence class representative (how is this different from root?)
    };
    static uint32_t cgid_ctr;
    struct {
        unsigned type       : 2;
        unsigned reloced    : 1;
        unsigned unused     : 29; } header;
    SymRef      symb;     // The symbol (if this is a symbol node) -- not sure this is necessary?
    PTRef       pterm;  // The proper term (if this is a term node)
    SERef        er;     // Either my eref or reference to the relocated one
    SERef        car;
    SERef        cdr;
    cgId        cid;            // The congruence id of the enode (defined also for symbols)

  public:
    // This is a trick to enable congruence data on only Enodes it is needed
    SCgData      cgdata[0];
    static SERef SERef_Nil;
    enum en_type { et_symb, et_list, et_term };
    // Constructor for symbols
    SEnode(SymRef, SERef);
    // Constructor for term and list nodes
    SEnode(SERef car_, SERef cdr_, en_type t, SEAllocator& ea, SERef er, Map<SigPair,SERef,SigHash,Equal<const SigPair&> >& sig_tab);
    en_type type        ()        const { return (en_type)header.type; }

    void relocate       (SERef e)        { header.reloced = 1; er = e; }
    bool reloced        ()        const { return header.reloced; }
    SERef relocation     ()        const { return er; }

    bool  isList        ()        const { return (en_type)header.type == et_list; }
    bool  isTerm        ()        const { return (en_type)header.type == et_term; }
    bool  isSymb        ()        const { return (en_type)header.type == et_symb; }
    SERef  getCar        ()        const { assert(type() != et_symb); return car; }
    SERef  getCdr        ()        const { assert(type() != et_symb); return cdr; }
    SymRef getSymb      ()        const { assert(type() == et_symb); return symb; }
    PTRef getTerm       ()        const { assert(type() != et_symb && type() != et_list); return pterm; }
    SERef  getRoot       ()        const { if (type() == et_symb) return er; else return cgdata->root; }
    void  setRoot       (SERef r)        { assert(type() != et_symb); cgdata->root = r; }
    SERef  getCgPtr      ()        const { return cgdata->cg_ptr; }
    void  setCgPtr      (SERef e)        { cgdata->cg_ptr = e; }
    CgId  getCid        ()        const { return cid; }
    void  setCid        (CgId id)       { cid = id; }
    SERef  getParent     ()        const { return cgdata->parent; }
    void  setParent     (SERef e)        { cgdata->parent = e; }
    int   getParentSize ()        const { return cgdata->parent_size; }
    void  setParentSize (int i)         { cgdata->parent_size = i; }
    SERef  getSameCdr    ()        const { return cgdata->same_cdr; }
    void  setSameCdr    (SERef e)        { cgdata->same_cdr = e; }
    SERef  getSameCar    ()        const { return cgdata->same_car; }
    void  setSameCar    (SERef e)        { cgdata->same_car = e; }
    SERef  getNext       ()        const { return cgdata->next; }
    void  setNext       (SERef n)        { cgdata->next = n; }
    int   getSize       ()        const { return cgdata->size; }
    void  setSize       (int i)         { cgdata->size = i; }
    friend class SEAllocator;
};

struct SERefHash {
    uint32_t operator () (const SERef& s) const {
        return (uint32_t)s.x; }
};

class SEAllocator : public RegionAllocator<uint32_t>
{
    static int senodeWord32Size(bool has_cgdata){
        if (has_cgdata) return (sizeof(SEnode) + sizeof(SEnode::SCgData))/sizeof(int32_t);
        else            return sizeof(SEnode)/sizeof(int32_t); }

    Map<SigPair,SERef,SigHash,Equal<const SigPair&> >* sig_tab;

 public:

    SEAllocator(uint32_t start_cap, Map<SigPair,SERef,SigHash,Equal<const SigPair&> >* st) : RegionAllocator<uint32_t>(start_cap), sig_tab(st) {}
    SEAllocator() {}

    void moveTo(SEAllocator& to){
        RegionAllocator<uint32_t>::moveTo(to); }

    // For symbols
    SERef alloc(SymRef sym) {
        assert(sizeof(SymRef)     == sizeof(uint32_t));
        assert(sizeof(SERef)     == sizeof(uint32_t));
        uint32_t v = RegionAllocator<uint32_t>::alloc(senodeWord32Size(false));
        SERef eid;
        eid.x = v;
        SEnode* tmp = new (lea(eid)) SEnode(sym, eid);
        tmp->header.type = Enode::et_symb;
        return eid;
    }

    // For terms and lists
    SERef alloc(SERef car, SERef cdr, SEnode::en_type t, PTRef ptr)
    {
        assert(sizeof(SymRef)     == sizeof(uint32_t));
        assert(sizeof(SERef)     == sizeof(uint32_t));

        bool has_cgdata = (t == SEnode::et_list) || (t == SEnode::et_term);
        uint32_t v = RegionAllocator<uint32_t>::alloc(senodeWord32Size(has_cgdata));
        SERef eid;
        eid.x = v;
        SEnode* tmp = new (lea(eid)) SEnode(car, cdr, t, *this, eid, *sig_tab);
        tmp->header.type = t;
        tmp->pterm = ptr;
        return eid;
    }

    SERef alloc(SEnode&) {
        assert(false);
        return SERef_Undef;
    }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    SEnode&       operator[](SERef r)         { return (SEnode&)RegionAllocator<uint32_t>::operator[](r.x); }
    const SEnode& operator[](SERef r) const   { return (SEnode&)RegionAllocator<uint32_t>::operator[](r.x); }
    SEnode*       lea       (SERef r)         { return (SEnode*)RegionAllocator<uint32_t>::lea(r.x); }
    const SEnode* lea       (SERef r) const   { return (SEnode*)RegionAllocator<uint32_t>::lea(r.x); }
    const SEnode& dbg       (int  r) const   { return (SEnode&)RegionAllocator<uint32_t>::operator[](r); }
    SERef         ael       (const SEnode* t) { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); SERef rf; rf.x = r; return rf; }

    void free(SERef eid)
    {
        SEnode& e = operator[](eid);
        if ((e.type() == SEnode::et_list) || (e.type() == SEnode::et_term))
            RegionAllocator<uint32_t>::free(senodeWord32Size(true));
        else
            RegionAllocator<uint32_t>::free(senodeWord32Size(false));

    }

    void reloc(SERef& er, SEAllocator& to)
    {
        SEnode& e = operator[](er);

        if (e.reloced()) { er = e.relocation(); return; }

        er = to.alloc(e);
        e.relocate(er);
    }

};

//
// A simpler congruence closure algorithm without backtracking and forbid lists
// for top-level propagation
//
class TopLevelPropagator {
    class Node {
      public:
        PTRef  tr;
        int    rank;
        Node*  parent;
        Node(PTRef d) : tr(d), rank(0), parent(this) {} // makeSet
    };
    class SERefPair {
      public:
        SERef x;
        SERef y;
        SERefPair(SERef x_, SERef y_) : x(x_), y(y_) {}
    };

    Logic&      logic;
    Cnfizer&    cnfizer;

    SEAllocator ea;
    Map<SigPair,SERef,SigHash,Equal<const SigPair&> > sigtab;
    Map<PTRef,SERef,PTRefHash,Equal<const PTRef> > termToSERef;
    Map<SymRef,SERef,SymRefHash,Equal<SymRef> > symToSERef;
    vec<SERefPair> pending;


    SERef       n_false;
    SERef       n_true;

    Map<PTRef, Node*, PTRefHash, Equal<PTRef> > PTRefToNode;
    PTRef find(PTRef p) const {return ea[termToSERef[p]].getTerm(); } // Return the root congruence element
    void merge(SERef xr, SERef yr);  // union
    bool contains(PTRef x, PTRef y); // term x contains an occurrence of y
    bool assertEq(PTRef eq);         // Add equivalence and propagate
  public:
    TopLevelPropagator(Logic& logic, Cnfizer& cnfizer);
    bool insertBindings(PTRef root); // Insert the top level variable
                                     // bindings implied by the formula
                                     // root
    bool substitute(PTRef& root);    // Substitute based on the
                                     // previously inserted bindings.
                                     // Return true if substitutions were performed
};

#endif
