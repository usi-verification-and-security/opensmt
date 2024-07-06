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
//
// Create the binding to a variable for the reference tr.  tr can be
// negated, in which case the binding is created to (not tr).  Safe to
// call several times for both tr and (not tr)
//
Var TermMapper::addBinding(PTRef tr) {
    assert(tr != PTRef_Undef);
    assert(varToTerm.size() == var_cnt);
    PTRef tr_p; // The purified term
    Var v;
    getVar(tr, tr_p, v);
    assert(v == var_Undef);
    v = Var(var_cnt++);
    assert(not hasLit(tr_p));
    auto termIndex = Idx(toId(tr_p));
    termToVar.growTo(termIndex + 1, var_Undef);
    termToVar[termIndex] = v;
    assert(varToTerm.size() == frozen.size());
    while (varToTerm.size() <= v) {
        varToTerm.push(PTRef_Undef);
        frozen.push(false);
    }
    varToTerm[v] = tr_p;
    return v;
}

void TermMapper::getTerm(PTRef r, PTRef & p, bool & sgn) const {
    sgn = false;
    while (logic.getPterm(r).symb() == logic.getSym_not()) {
        r = logic.getPterm(r)[0];
        sgn = !sgn;
    }
    p = r;
}

Lit TermMapper::getLit(PTRef r) const {
    bool sgn;
    PTRef p;
    getTerm(r, p, sgn);
    Var v = var_Undef;
    bool found = peekVar(p, v);
    assert(found);
    (void)found;
    return mkLit(v, sgn);
}

void TermMapper::getVar(PTRef r, PTRef & p, Var & v) const {
    bool sgn;
    getTerm(r, p, sgn);
    v = var_Undef;
    peekVar(p, v);
}

Var TermMapper::getVar(PTRef r) const {
    Var v = var_Undef;
    PTRef p;
    getVar(r, p, v);
    return v;
}

Lit const TermMapper::getOrCreateLit(PTRef ptr) {
    PTRef p_tr;
    bool sgn;
    Var v = var_Undef;
    getTerm(ptr, p_tr, sgn);
    peekVar(p_tr, v);
    if (v == var_Undef) {
        assert(logic.hasSortBool(p_tr));
        v = this->addBinding(p_tr);
    }
    Lit l = mkLit(v, sgn);
    return l;
}

bool TermMapper::peekVar(PTRef positiveTerm, Var & v) const {
    assert(not logic.isNot(positiveTerm));
    auto id = Idx(toId(positiveTerm));
    v = id < termToVar.size_() ? termToVar[id] : var_Undef;
    return v != var_Undef;
}

PTRef TermMapper::toPositive(PTRef term) const {
    bool sign;
    PTRef pos;
    getTerm(term, pos, sign);
    return pos;
}
