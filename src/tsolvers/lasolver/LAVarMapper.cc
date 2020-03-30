//
// Created by prova on 06.09.19.
//

#include "LAVarMapper.h"
#include "LALogic.h"

LVRef LAVarMapper::registerNewMapping(LVRef lv, PTRef e_orig) {
    assert(!hasVar(e_orig));
    assert(!logic.isNegated(e_orig));
    if (lv.x >= static_cast<unsigned int>(laVarToPTRef.size())) {
        laVarToPTRef.growTo(lv.x+1, PTRef_Undef);
    }

    laVarToPTRef[lv.x] = e_orig;

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

void LAVarMapper::addLeqVar(PTRef leq_tr, LVRef v)
{
    Pterm& leq_t = logic.getPterm(leq_tr);
    int idx = Idx(leq_t.getId());
    for (int i = leqToLavar.size(); i <= idx; i++)
        leqToLavar.push(LVRef_Undef);
    leqToLavar[idx] = v;
}

bool LAVarMapper::hasVar(PTRef tr) { return hasVar(logic.getPterm(tr).getId()); }

LVRef  LAVarMapper::getVarByPTId(PTId i) const { return ptermToLavar[Idx(i)]; }

LVRef  LAVarMapper::getVarByLeqId(PTId i) const { return leqToLavar[Idx(i)]; }

bool   LAVarMapper::hasVar(PTId i) { return static_cast<unsigned int>(ptermToLavar.size()) > Idx(i) && ptermToLavar[Idx(i)] != LVRef_Undef; }

