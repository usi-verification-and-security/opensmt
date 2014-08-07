/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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


#ifndef TERMMAPPER_H
#define TERMMAPPER_H
#include "Map.h"
#include "SolverTypes.h"
#include "Pterm.h"
#include "Logic.h"
class TermMapper {
  private:
    Logic&      logic;
  public:
    TermMapper(Logic& l) : logic(l) {}

    vec<PTRef>                                varToTerm;
    vec<SymRef>                               varToTheorySymbol;
    Map<PTRef,Var,PTRefHash,Equal<PTRef> >    termToVar;
    Map<PTRef,bool,PTRefHash,Equal<PTRef> >   theoryTerms;

    // Return a "purified" term by removing sequence of nots.  sgn is false if sequence length is even, and true if it odd
    void getTerm(PTRef tr, PTRef& tr_clean, bool& sgn) const;
    Var  getVar(PTRef)    const;
    Lit  getLit(PTRef)    const;
    bool hasLit(PTRef tr) const { return termToVar.contains(tr); }
#ifdef PEDANTIC_DEBUG
    Var  getVarDbg(int r) const { PTRef tr; tr = r; return termToVar[tr]; }
#endif
};

#endif
