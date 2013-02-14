// Strongly MiniSat inspired implementation for proper terms
#ifndef PTERM_H
#define PTERM_H

#include "Vec.h"
#include "Alloc.h"
#include "Term.h"

typedef RegionAllocator<uint32_t>::Ref PTRef;

typedef TRefHash PTRefHash;
// These are redefinitions...
//struct PTRefHash {
//    uint32_t operator () (const PTRef s) const {
//        return (uint32_t)s; }
//};

//template <>
//struct Equal<const PTRef> {
//    bool operator() (const PTRef s1, const PTRef s2) { return s1 == s2; }
//};


typedef uint32_t TRef;
typedef uint32_t PTId; // Used as an array index

// args[0].sort is the return sort, rest are arguments.
class Pterm {
    struct {
        unsigned type       : 3;
        unsigned has_extra  : 1;
        unsigned reloced    : 1;
        unsigned noscoping  : 1;
        unsigned size       : 26; }     header;
    PTId                                id;
    TRef                                sym;
    // This has to be the last
    PTRef                               args[0]; // Either the terms or the relocation reference


    friend class PtermAllocator;
    friend class PTStore;
  public:
    // Note: do not use directly (no memory allocation for args)
    Pterm(const TRef sym_, const vec<PTRef>& ps) : sym(sym_) {
        header.type      = 0;
        header.has_extra = 0;
        header.reloced   = 0;
        header.noscoping = 0;           // This is an optimization to avoid expensive name lookup on logic operations
        header.size      = ps.size();

        for (int i = 0; i < ps.size(); i++) args[i] = ps[i]; }
  public:

    // -- use this as a wrapper:
    Pterm* Pterm_new(TRef sym, vec<PTRef>& ps, bool left_assoc = false, bool right_assoc = false, bool chainable = false, bool pairwise = false) {
        assert(sizeof(PTRef) == sizeof(uint32_t));
        assert(sizeof(PTId)  == sizeof(uint32_t));
        assert(sizeof(TRef)  == sizeof(uint32_t));
        void* mem = malloc(sizeof(header) + sizeof(PTId) + +sizeof(TRef) + sizeof(PTRef)*ps.size());

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

    int      size        ()      const   { return header.size; }
    PTRef    operator [] (int i) const   { return args[i]; }
    TRef     symb        ()      const   { return sym; }
    bool     has_extra   ()      const   { return false; }
    bool     reloced     ()      const   { return header.reloced; }
    TRef     relocation  ()      const   { return args[0]; }
    void     relocate    (TRef t)        { header.reloced = 1; args[0] = t; }
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

};

const PTRef PTRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;

class PtermAllocator : public RegionAllocator<uint32_t>
{
    static int ptermWord32Size(int size){
        return (sizeof(Pterm) + (sizeof(PTRef) * size )) / sizeof(uint32_t); }
 public:
    bool extra_term_field;

    PtermAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), extra_term_field(false){}
    PtermAllocator() : extra_term_field(false){}

    void moveTo(PtermAllocator& to){
        to.extra_term_field = extra_term_field;
        RegionAllocator<uint32_t>::moveTo(to); }

    PTRef alloc(const TRef sym, const vec<PTRef>& ps, bool extra = false)
    {
        assert(sizeof(PTRef) == sizeof(uint32_t));

        PTRef tid = RegionAllocator<uint32_t>::alloc(ptermWord32Size(ps.size()));
        new (lea(tid)) Pterm(sym, ps);

        return tid;
    }

    PTRef alloc(Pterm&, bool) { assert(false); return PTRef_Undef; }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Pterm&       operator[](Ref r)         { return (Pterm&)RegionAllocator<uint32_t>::operator[](r); }
    const Pterm& operator[](Ref r) const   { return (Pterm&)RegionAllocator<uint32_t>::operator[](r); }
    Pterm*       lea       (Ref r)         { return (Pterm*)RegionAllocator<uint32_t>::lea(r); }
    const Pterm* lea       (Ref r) const   { return (Pterm*)RegionAllocator<uint32_t>::lea(r); }
    Ref          ael       (const Pterm* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

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

#endif
