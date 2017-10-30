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

#include "Global.h"
#include "Pterm.h"
#include "Delta.h"
#include "LARow.h"
#include "LAColumn.h"
#include "LRALogic.h"
#include "Deductions.h"

class LRASolver;
class LAVarStore;

struct LAVarBound
{
    PTRef e;
    Delta * delta;
    BoundT bound_type;
    bool reverse;
    bool active;
    LAVarBound( Delta * _delta, PTRef _e, BoundT _boundType, bool _reverse );
    bool operator==( const LAVarBound &b );
};

struct LVRef {
    uint32_t x;
    void operator= (uint32_t v) { x = v; }
    inline friend bool operator== (const LVRef& a1, const LVRef& a2) { return a1.x == a2.x; }
    inline friend bool operator!= (const LVRef& a1, const LVRef& a2) { return a1.x != a2.x; }
};

static struct LVRef PVRef_Undef = { INT32_MAX };

//
// Class to store the term of constraints as a column of Simplex method tableau
//
class LAVar
{
    friend class LAVarAllocator;

private:
    struct {
        unsigned basic   : 1;  // Is the node basic or non-basic
        unsigned reloced : 1;
        unsigned skp     : 1;
        unsigned id      : 29; // The unique id
    } header;

    PTRef e;          // The term in the SMT world
    int column_id;    //
    int row_id;       //

    unsigned curr_ub;      // The current upper bound, idx to bounds table
    unsigned curr_lb;      // The current lower bound, idx to bounds table
    LABoundListRef bounds; // The bounds of this variable

    union { PolyRef poly; OccRef occs; }; // If basic, the polynomial.  If not, the occs.

public:
    // Constructor.  The e_orig from SMT world, the bounds list, and a unique id
    LAVar(PTRef e_orig, unsigned id);
    void skip()     const   { return header.skp;                }
    void setSkip()          { header.skip = true;               }
    void clrSkip()          { header.skip = false;              }
    int  getRowId() const   { assert(!basic); return row_id;    }
    void setRowId(int i)    { assert(!basic); row_id = i;       }
    int getColId()  const   { assert(basic);  return column_id; }
    void setColId(int i)    { assert(basic);  col_id = i;       }

    int ubound()   { return curr_ub; }
    int lbound()   { return curr_lb; }
    unsigned setUbound(int i) { curr_ub = i; }
    unsigned setLbound(int i) { curr_lb = i; }
    LABoundListRef getBounds() { return bounds; }

    inline bool isBasic( );               // Checks if current LAVar is Basic in current solver state
    inline bool isUnbounded( );           // Check if LAVar has no bounds at all (it can be eliminated if possible).
    inline bool isModelInteger( );        // Check if LAVar has an integer model.

    inline int ID( );                     // Return the ID of the LAVar
    inline void setNonbasic();            // Make LAVar Nonbasic
    inline void setBasic( int row );      // Make LAVar Basic and set the row number it corresponds

    // Binded rows system
    OccListRef getBindedRowsRef() const { assert(!basic); return occs; }
    PolyRef    getPolyRef() const       { assert(basic); return poly; }
    void       setPolyRef(PolyRef r)    { assert(basic); poly = r; }
    // structure to perform comparison of two LAVarBounds
    struct LAVarBounds_ptr_cmp
    {
        bool operator()( LAVarBound lhs, LAVarBound rhs );
    };
};

bool LAVar::isBasic( )
{
    return header.basic;;
}


bool LAVar::isNonbasic( )
{
    return !isBasic( );
}

int LAVar::getID( )
{
    return header.id;
}

int LAVar::getRowId( )
{
    return row_id;
}

void LAVar::setNonbasic( )
{
    row_id = -1;
    header.basic = false;
}

void LAVar::setBasic( int row )
{
    row_id = row;
    header.basic = true;
}


class LAVarAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_vars;
    static int lavarWord32Size() {
        return (sizeof(LAVar)) / sizeof(uint32_t); }
public:
    LAVarAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_vars(0) {}
    LAVarAllocator()                   : n_vars(0) {}
    unsigned getNumVars() const { return n_vars; }

    LVRef alloc(bool basic, PTRef e)
    {
        uint32_t v = RegionAllocator<uint32_t>::alloc(lavarWord32Size());
        LVRef id = {v};
        new (lea(id)) LAVar(e, basic, n_vars++);
        return id;
    }
    LABound&       operator[](LABoundRef r)       { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    const LABound& operator[](LABoundRef r) const { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
};

class LAVarStore
{
private:
    int             column_count;               // Counter to create ID for LAVar
    int             row_count;                  // Counter for rows keep track of basic variables
    vec<LAVar*>     lavars;
    vector<Real*>&  numbers_pool;
    LAVarAllocator& lva;
public:
    LAVarStore(LAVarAllocator& lva, vector<Real*>& numbers_pool) : column_count(0), row_count(0), lva(lva) {}
    ~LAVarStore();
    void   clear();
    LAVar* getNewVar(PTRef e_orig = PTRef_Undef);
    void   notifyRow(LAVar* s);
    void   resetVars(); // Set the polynomials of the vars to the initial state
    int    numVars() const;
    void   printVars() const;
};


#endif
