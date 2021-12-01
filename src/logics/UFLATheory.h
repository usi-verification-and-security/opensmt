/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2016 Antti Hyvarinen

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

#ifndef UFLRATheory_h
#define UFLRATheory_h

#include "Theory.h"
#include "UFLATHandler.h"
#include "ArithLogic.h"

class UFLATheory : public Theory
{
  private:
    ArithLogic &  logic;
    UFLATHandler uflatshandler;
  public:
    UFLATheory(SMTConfig& c, ArithLogic & logic)
        : Theory(c)
        , logic(logic)
        , uflatshandler(c, logic)
    { }
    virtual ArithLogic&       getLogic() override { return logic; }
    virtual const ArithLogic& getLogic() const override { return logic; }
    virtual UFLATHandler&  getTSolverHandler() override { return uflatshandler; }
    virtual bool            simplify(const vec<PFRef>&, PartitionManager&, int) override;

protected:
    PTRef purify(PTRef fla);
    PTRef splitArithmeticEqualities(PTRef fla);
    PTRef addInterfaceClauses(PTRef fla);
};

#endif
