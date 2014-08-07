/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
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
