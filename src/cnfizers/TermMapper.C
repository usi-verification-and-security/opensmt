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


