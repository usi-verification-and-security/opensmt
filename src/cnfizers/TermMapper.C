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


#include "TermMapper.h"

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
    assert(termToVar.contains(p));
#endif
    return Lit(termToVar[p], sgn);
}

Var TermMapper::getVar(PTRef r) const {
    bool sgn;
    PTRef p;
    getTerm(r, p, sgn);
    return termToVar[p];
}


