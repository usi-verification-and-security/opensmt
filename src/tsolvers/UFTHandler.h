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

#ifndef UFTHandler_h
#define UFTHandler_h

//#include "THandler.h"
#include "Logic.h"
#include "TSolverHandler.h"
#include "Egraph.h"

class UFTHandler : public TSolverHandler
{
  private:
    Logic& logic;
    Egraph* egraph;
//  protected:
//    const vec<int>& getSolverSchedule() const;
  public:
    UFTHandler(SMTConfig& c, Logic& l, vec<DedElem>& d);
    virtual ~UFTHandler();
    bool assertLit_special(PtAsgn a);
    void fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs);
    Logic& getLogic();

#ifdef PRODUCE_PROOF
    TheoryInterpolator* getTheoryInterpolator()
    {
        return egraph->getTheoryInterpolator();
    }

    PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels)
    {
        return egraph->getInterpolant(mask, labels);
    }
#endif
};

#endif
