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


#include "TermMapper.h"

void TermMapper::addBinding(Var v, PTRef tr)
{
    assert(varToTerm.size() == v && varToTheorySymbol.size() == v);
    logic.getPterm(tr).setVar(v);
    if (tr != PTRef_Undef) {
        varToTheorySymbol.push(logic.getSymRef(tr));
        varToTerm.push(tr);
    } else {
        assert(false);
    }
}

void TermMapper::getTerm(PTRef r, PTRef& p, bool& sgn) const {
    sgn = false;
    while (logic.term_store[r].symb() == logic.getSym_not()) {
        r = logic.term_store[r][0];
        sgn = !sgn;
    }
    p = r;
}

Lit TermMapper::getLit(PTRef r) const {
    bool sgn;
    PTRef p;
    getTerm(r, p, sgn);
#ifdef PEDANTIC_DEBUG
    assert(logic.getPterm(p).hasVar());
#endif
    return mkLit(logic.getPterm(p).getVar(), sgn);
}

Var TermMapper::getVar(PTRef r) const {
    bool sgn;
    PTRef p;
    getTerm(r, p, sgn);
    return logic.getPterm(p).getVar();
}


