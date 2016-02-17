/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2015 Antti Hyvarinen
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
#ifndef LRATHandler_H
#define LRATHandler_H

//#include "THandler.h"
#include "LRASolver.h"
#include "LRALogic.h"
#include "TSolverHandler.h"
#include "Egraph.h"

class LRATHandler : public TSolverHandler
{
  private:
    LRALogic& logic;
    LRASolver *lrasolver;
  public:
    LRATHandler(SMTConfig& c, LRALogic& l, vec<DedElem>& d);
    virtual ~LRATHandler();
    void fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs);
    bool assertLit_special(PtAsgn);
    Logic& getLogic();

#ifdef PRODUCE_PROOF
    PTRef getInterpolants(const ipartitions_t& m)
    {
        return PTRef_Undef;
    }
#endif
};

#endif
