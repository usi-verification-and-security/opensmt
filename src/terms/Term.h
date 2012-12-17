// Strongly MiniSat inspired implementation for Terms
#ifndef TERM_H
#define TERM_H

#include "Vec.h"
#include "Alloc.h"
#include "Sort.h"

typedef RegionAllocator<uint32_t>::Ref TRef;

typedef uint32_t SRef;
typedef uint32_t TId; // Used as an array index

// args[0].sort is the return sort, rest are arguments.
class Term {
    struct {
        unsigned type       : 3;
        unsigned learnt     : 1;
        unsigned has_extra  : 1;
        unsigned reloced    : 1;
        unsigned noscoping  : 1;
        unsigned size       : 25; }     header;
    TId                                 id;
    // This has to be the last
    union { SRef sort; TRef rel;  }     args[0];


    friend class TermAllocator;
    friend class TStore;
  public:
    // Note: do not use directly (no memory allocation for args)
    Term(const vec<TRef>& ps) {
        header.type      = 0;
        header.learnt    = 0;
        header.has_extra = 0;
        header.reloced   = 0;
        header.noscoping = 0;           // This is an optimization to avoid expensive name lookup on logic operations
        header.size      = ps.size();

        for (int i = 0; i < ps.size(); i++) args[i].sort = ps[i]; }
  public:

    // -- use this as a wrapper:
    Term* Term_new(vec<SRef>& ps, bool left_assoc = false, bool right_assoc = false, bool chainable = false, bool pairwise = false) {
        assert(sizeof(SRef) == sizeof(uint32_t));
        void* mem = malloc(sizeof(header) + sizeof(TId) + sizeof(uint32_t)*ps.size());
        //new (mem) Term(ps);
        assert(left_assoc + right_assoc + chainable + pairwise <= 1);
        if (left_assoc == true)
            header.type = 1;
        else if (right_assoc == true)
            header.type = 2;
        else if (chainable == true)
            header.type = 3;
        else if (pairwise == true)
            header.type = 4;
        return new (mem) Term(ps); }

    int      size        ()      const   { return header.size; }
    SRef     operator [] (int i) const   { return args[i+1].sort; }
    SRef     rsort       ()      const   { return args[0].sort; }
    bool     has_extra   ()      const   { return false; }
    bool     reloced     ()      const   { return header.reloced; }
    TRef     relocation  ()      const   { return args[0].rel; }
    bool     learnt      ()      const   { return header.learnt; }
    void     relocate    (TRef t)        { header.reloced = 1; args[0].rel = t; }
    uint32_t type        ()      const   { return header.type; }
    void     type        (uint32_t m)    { header.type = m; }
    bool     left_assoc  ()      const   { return header.type == 1; }
    bool     right_assoc ()      const   { return header.type == 2; }
    bool     chainable   ()      const   { return header.type == 3; }
    bool     pairwise    ()      const   { return header.type == 4; }
    bool     noScoping   ()      const   { return header.noscoping; }
    uint32_t nargs       ()      const   { return size() - 1; }

    bool     setLeftAssoc ()             { if (header.type != 0) return false; return (header.type = 1); }
    bool     setRightAssoc()             { if (header.type != 0) return false; return (header.type = 2); }
    bool     setChainable ()             { if (header.type != 0) return false; return (header.type = 3); }
    bool     setPairwise  ()             { if (header.type != 0) return false; return (header.type = 4); }
    void     setNoScoping ()             { header.noscoping = 1; }

    int      getId() const { return id; }
    void     setId(int i) { id = i; }

};

const TRef TRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;
const TRef TRef_Nil = TRef_Undef-1;

class TermAllocator : public RegionAllocator<uint32_t>
{
    static int termWord32Size(int size){
        return (sizeof(Term) + (sizeof(SRef) * size )) / sizeof(uint32_t); }
 public:
    bool extra_term_field;

    TermAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), extra_term_field(false){}
    TermAllocator() : extra_term_field(false){}

    void moveTo(TermAllocator& to){
        to.extra_term_field = extra_term_field;
        RegionAllocator<uint32_t>::moveTo(to); }

    template<class Sorts>
    TRef alloc(const Sorts& ps, bool)
    {
        assert(sizeof(SRef)     == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));

        TRef tid = RegionAllocator<uint32_t>::alloc(termWord32Size(ps.size()));
        new (lea(tid)) Term(ps);

        return tid;
    }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Term&       operator[](Ref r)        { return (Term&)RegionAllocator<uint32_t>::operator[](r); }
    const Term& operator[](Ref r) const  { return (Term&)RegionAllocator<uint32_t>::operator[](r); }
    Term*       lea       (Ref r)        { return (Term*)RegionAllocator<uint32_t>::lea(r); }
    const Term* lea       (Ref r) const  { return (Term*)RegionAllocator<uint32_t>::lea(r); }
    Ref         ael       (const Term* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(TRef tid)
    {
        Term& t = operator[](tid);
        RegionAllocator<uint32_t>::free(termWord32Size(t.size()));
    }

    void reloc(TRef& tr, TermAllocator& to)
    {
        Term& t = operator[](tr);

        if (t.reloced()) { tr = t.relocation(); return; }

        tr = to.alloc(t, t.learnt());
        t.relocate(tr);

        // Copy extra data-fields:
        to[tr].type(t.type());
//        if (to[tr].learnt())         to[tr].activity() = t.activity();
//        else if (to[tr].has_extra()) to[tr].calcAbstraction();
    }
};

#endif
