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
#include <vector>

class LRASolver;
class LAVarStore;
class LALogic;


class LAVarStore
{
private:
    std::vector<PTRef>      lavars;
    vec<LVRef>      leqToLavar;              // Maps Pterm constraints to solver's real variables.
    vec<LVRef>      ptermToLavar;            // Maps Pterm variables to solver's real variables
    LALogic&        logic;
public:
    LAVarStore(LALogic & logic) : logic(logic) {}
    inline void   clear() {};
    LVRef  getNewVar(PTRef e_orig);
    LVRef  getVarByPTId(PTId i);
    void   addLeqVar(PTRef leq_tr, LVRef v); // Adds a binding from leq_tr to the "slack var" v
    LVRef  getVarByLeqId(PTId i);
    bool   hasVar(PTId i) ;
    bool   hasVar(PTRef tr);
    int    numVars() const ;
    inline PTRef getVarPTRef(LVRef ref) const { return lavars[ref.x]; }
};


#endif
