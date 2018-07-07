/*********************************************************************
Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
      , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

OpenSMT2 -- Copyright (C) 2008-2012, Roberto Bruttomesso

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

#ifndef LAVAR_H
#define LAVAR_H

#include "Deductions.h"
#include "PtStructs.h"
#include "LARefs.h"
#include "Pterm.h"

class LRASolver;
class LAVarStore;
class LALogic;


//
// Class to store the term of constraints as a column of Simplex method tableau
//
class LAVar
{
    friend class LAVarAllocator;

private:
    struct {
        bool basic   : 1;  // Is the node basic or non-basic
        bool reloced : 1;
        bool skp     : 1;
        unsigned id      : 29; // The unique id
    } header;

    PTRef e;               // The term in the SMT world
    int col_id;            // Column id
    int row_id;            // Row id

//    BoundIndex curr_ub;      // The current upper bound, idx to bounds table
//    BoundIndex curr_lb;      // The current lower bound, idx to bounds table
//    LABoundListRef bounds; // The bounds of this variable

    PolyRef poly;          // Polynomial
    OccListRef occs;       // The occurrences in polynomials.

public:
    // Constructor.  The e_orig from SMT world, the bounds list, and a unique id
    LAVar(PTRef e_orig, unsigned id);
    bool skip    ()      const;// { return header.skp;                }
    void setSkip ()     ;//       { header.skp = true;                }
    void clrSkip ()       ;//     { header.skp = false;               }
    int  getRowId()      const;// { return row_id; }
    void setRowId(int i)      ;// { row_id = i;    }
    int  getColId()      const;// { return col_id; }
    void setColId(int i)     ;//  { col_id = i;    }

//    BoundIndex ubound()             const { return curr_ub; }
//    BoundIndex lbound()             const { return curr_lb; }
//    void setUbound(BoundIndex i)            { curr_ub = i; }
//    void setLbound(BoundIndex i)            { curr_lb = i; }
//    LABoundListRef getBounds()      const { return bounds; }
//    void setBounds(LABoundListRef l)      { bounds = l; }

    //inline bool isBasic()           const { return header.basic; } // Checks if current LAVar is Basic in current solver state

    inline int  ID()                const;// { return header.id; } // Return the ID of the LAVar
    inline void setNonbasic();           // Make LAVar Nonbasic
    inline void setBasic();              // Make LAVar Basic

    // Binded rows system
    OccListRef getBindedRowsRef() const   ;//    { return occs; }
    void       setBindedRowsRef(OccListRef r) ;//{ occs = r; }
    PolyRef    getPolyRef()       const    ;//   { return poly; }
    void       setPolyRef(PolyRef r)       ;//   { poly = r; }

    PTRef      getPTRef()         const   ;//    { return e; }
};

/*
void LAVar::setNonbasic()
{
    header.basic = false;
}

void LAVar::setBasic()
{
    header.basic = true;
}
*/

class LAVarAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_vars;
    static int lavarWord32Size();/* {
        return (sizeof(LAVar)) / sizeof(uint32_t); }*/
public:
    LAVarAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_vars(0) {}
    LAVarAllocator()                   : n_vars(0) {}
    unsigned getNumVars() const;// { return n_vars; }

    LVRef alloc(PTRef e);
    /*{
        uint32_t v = RegionAllocator<uint32_t>::alloc(lavarWord32Size());
        LVRef id = {v};
        new (lea(id)) LAVar(e, n_vars++);
        return id;
    }*/
    LAVar&       operator[](LVRef r) ;//      { return (LAVar&)RegionAllocator<uint32_t>::operator[](r.x); }
    const LAVar& operator[](LVRef r) const ;//{ return (LAVar&)RegionAllocator<uint32_t>::operator[](r.x); }
    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    LAVar*       lea       (LVRef r)    ;//     { return (LAVar*)RegionAllocator<uint32_t>::lea(r.x); }
    const LAVar* lea       (LVRef r) const  ;// { return (LAVar*)RegionAllocator<uint32_t>::lea(r.x); }
    LVRef        ael       (const LAVar* t) ;// { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LVRef rf; rf.x = r; return rf; }
    void         free      (LVRef r)        ;// { RegionAllocator::free(lavarWord32Size()); }
    void         clear() {}
    // Debug stuff
    char*        printVar (LVRef r)  const ;//  { char* str; asprintf(&str, "v%d", r.x);  return str; }
};

class LAVarStore
{
private:
    vec<LVRef>      lavars;
    LAVarAllocator& lva;
    vec<LVRef>      leqToLavar;              // Maps Pterm constraints to solver's real variables.
    vec<LVRef>      ptermToLavar;            // Maps Pterm variables to solver's real variables
    LALogic&       logic;
public:
    LAVarStore(LAVarAllocator& lva, LALogic& logic) : lva(lva), logic(logic) {}
    inline void   clear() {};
    LVRef  getNewVar(PTRef e_orig);
    LVRef  getVarByPTId(PTId i);// { return ptermToLavar[Idx(i)]; }
    void   addLeqVar(PTRef leq_tr, LVRef v); // Adds a binding from leq_tr to the "slack var" v
    LVRef  getVarByLeqId(PTId i);// { return leqToLavar[Idx(i)]; }
    bool   hasVar(PTId i) ;//{ return ptermToLavar.size() > Idx(i) && ptermToLavar[Idx(i)] != LVRef_Undef; }
    bool   hasVar(PTRef tr);
    int    numVars() const ;//{ return lavars.size(); }
    void   remove(LVRef r) ;//{ lva.free(r); };
    LVRef  getVarByIdx(unsigned i) ;//{ return lavars[i]; }
};


#endif
