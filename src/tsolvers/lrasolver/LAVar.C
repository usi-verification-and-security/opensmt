/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
 Antti Hyvarinen <antti.hyvarinen@gmail.com>

 OpenSMT2 -- Copyright (C) 2012 - 2015, Antti Hyvarinen
                           2008 - 2012, Roberto Bruttomesso

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

#include "LAVar.h"
#include "LRALogic.h"



LAVar::LAVar(PTRef e, unsigned id)
        : e(e)
        , col_id(-1)
        , row_id(-1)
        , poly(PolyRef_Undef)
        , occs(OccListRef_Undef)
{
    header.basic = 0;
    header.reloced = 0;
    header.skp = 0;
    header.id = id;
}

LVRef LAVarStore::getNewVar(PTRef e_orig) {
    assert(!logic.isNegated(e_orig));
    LVRef lv = lva.alloc(e_orig);
    while (lavars.size() <= lva[lv].ID())
        lavars.push(LVRef_Undef);
    lavars[lva[lv].ID()] = lv;

    PTId id_pos = logic.getPterm(e_orig).getId();
    PTId id_neg = logic.getPterm(logic.mkNumNeg(e_orig)).getId();
    assert(!hasVar(id_pos));
    int max_id = std::max(Idx(id_pos), Idx(id_neg));

    if (max_id >= ptermToLavar.size())
        ptermToLavar.growTo(max_id+1, LVRef_Undef);

    assert(ptermToLavar[Idx(id_pos)] == ptermToLavar[Idx(id_neg)]);

    ptermToLavar[Idx(id_pos)] = lv;
    ptermToLavar[Idx(id_neg)] = lv;

    return lv;
}

void LAVarStore::addLeqVar(PTRef leq_tr, LVRef v)
{
    Pterm& leq_t = logic.getPterm(leq_tr);
    int idx = Idx(leq_t.getId());
    for (int i = leqToLavar.size(); i <= idx; i++)
        leqToLavar.push(LVRef_Undef);
    leqToLavar[idx] = v;
}

bool LAVarStore::hasVar(PTRef tr)
{ return hasVar(logic.getPterm(tr).getId()); }
