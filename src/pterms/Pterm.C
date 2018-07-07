// Strongly MiniSat inspired implementation for proper terms
#ifndef PTERM_H
#define PTERM_H

#include "Pterm.h"

    PtAsgn Pterm::getExpReason       () const { return exp_reason; }
    PTRef  Pterm::getExpParent       () const { return exp_parent; }
    PTRef  Pterm::getExpRoot         () const { return exp_root; }
    int    Pterm::getExpTimeStamp    () const { return exp_time_stamp; }

    void Pterm::setExpReason     (PtAsgn r)     { exp_reason = r; }
    void Pterm::setExpParent     (PTRef r)      { exp_parent = r; }
    void Pterm::setExpRoot       (PTRef r)      { exp_root   = r; }
    void Pterm::setExpTimeStamp  (const int t)  { exp_time_stamp   = t; }


    Pterm::Pterm() {
        header.type      = 0;
        header.has_extra = 0;
        header.reloced   = 0;
        header.noscoping = 0;           // This is an optimization to avoid expensive name lookup on logic operations
        header.size      = 0;

        var              = var_Undef;

    }

    Pterm    Pterm::operator=   (Pterm)         { assert(false); return *this; }

    int      Pterm::size        ()          const   { return header.size; }

    const PTRef& Pterm::operator [] (int i) const   { assert(i < size()); return args[i]; }
    PTRef&       Pterm::operator [] (int i)         { assert(i < size()); return args[i]; }

    SymRef   Pterm::symb        ()      const   { return sym; }
    bool     Pterm::has_extra   ()      const   { return false; }
    bool     Pterm::reloced     ()      const   { return header.reloced; }
    PTRef    Pterm::relocation  ()      const   { return args[0]; }
    void     Pterm::relocate    (PTRef t)       { header.reloced = 1; args[0] = t; }
    uint32_t Pterm::type        ()      const   { return header.type; }
    void     Pterm::type        (uint32_t m)    { header.type = m; }
    bool     Pterm::left_assoc  ()      const   { return header.type == 1; }
    bool     Pterm::right_assoc ()      const   { return header.type == 2; }
    bool     Pterm::chainable   ()      const   { return header.type == 3; }
    bool     Pterm::pairwise    ()      const   { return header.type == 4; }
    bool     Pterm::noScoping   ()      const   { return header.noscoping; }
    uint32_t Pterm::nargs       ()      const   { return size(); }

    bool     Pterm::setLeftAssoc ()             { if (header.type != 0) return false; return (header.type = 1); }
    bool     Pterm::setRightAssoc()             { if (header.type != 0) return false; return (header.type = 2); }
    bool     Pterm::setChainable ()             { if (header.type != 0) return false; return (header.type = 3); }
    bool     Pterm::setPairwise  ()             { if (header.type != 0) return false; return (header.type = 4); }
    void     Pterm::setNoScoping ()             { header.noscoping = 1; }

    PTId     Pterm::getId() const { return id; }
    void     Pterm::setId(int i) { id.x = i; }

    void     Pterm::setVar(Var v)   { var = v; }
    void     Pterm::clearVar()      { var = var_Undef; }
    Var      Pterm::getVar() const  { return var; }
    bool     Pterm::hasVar() const  { return var != var_Undef; }

    void     Pterm::shrink(int s)               { header.size -= s; }


    inline friend bool PtChild::operator== (const PtChild& a1, const PtChild& a2) { return (a1.tr == a2.tr) && (a1.parent == a2.parent) && (a1.pos == a2.pos); }
    inline friend bool PtChild::operator!= (const PtChild& a1, const PtChild& a2) { return (a1.tr != a2.tr) || (a1.parent != a2.parent) || (a1.pos != a2.pos); }
//    inline friend bool operator< (const PTRef& a1, const PTRef& a2)    { return a1.x < a2.x;  }


    void PtermAllocator::setNumTerms(int i) { n_terms = i; }
    static int PtermAllocator::ptermWord32Size(int size){ return (sizeof(Pterm) + (sizeof(PTRef) * size )) / sizeof(uint32_t); }
    int PtermAllocator::getNumTerms() const { return n_terms; }

    void PtermAllocator::moveTo(PtermAllocator& to){
        to.n_terms = n_terms;
        RegionAllocator<uint32_t>::moveTo(to); }

    PTRef PtermAllocator::alloc(const SymRef sym, const vec<PTRef>& ps, bool extra = false)
    {
        assert(sizeof(PTRef) == sizeof(uint32_t));

        uint32_t v = RegionAllocator<uint32_t>::alloc(ptermWord32Size(ps.size()));
        PTRef tid = {v};
        new (lea(tid)) Pterm(sym, ps, tid);
        operator[](tid).setId(n_terms++);

        return tid;
    }

    PTRef PtermAllocator::alloc(Pterm&, bool) { assert(false); return PTRef_Undef; }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Pterm&       PtermAllocator::operator[](PTRef r)         { return (Pterm&)RegionAllocator<uint32_t>::operator[](r.x); }
    const Pterm& PtermAllocator::operator[](PTRef r) const   { return (Pterm&)RegionAllocator<uint32_t>::operator[](r.x); }
    Pterm*       PtermAllocator::lea       (PTRef r)         { return (Pterm*)RegionAllocator<uint32_t>::lea(r.x); }
    const Pterm* PtermAllocator::lea       (PTRef r) const   { return (Pterm*)RegionAllocator<uint32_t>::lea(r.x); }
    PTRef        PtermAllocator::ael       (const Pterm* t)  { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); PTRef rf; rf.x = r; return rf; }

    void PtermAllocator::free(PTRef tid)
    {
        Pterm& t = operator[](tid);
        RegionAllocator<uint32_t>::free(ptermWord32Size(t.size()));
    }

    void PtermAllocator::reloc(PTRef& tr, PtermAllocator& to)
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
