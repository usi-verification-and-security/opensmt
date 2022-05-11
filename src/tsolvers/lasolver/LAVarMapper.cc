/*
 *  Copyright (c) 2019-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2019-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#include "LAVarMapper.h"
#include "ArithLogic.h"

/**
 * Remembers the mapping between a linear term (PTRef) and LA var (LVRef).
 *
 * The PTRef is expect to be a positive term, i.e., its leading variable does NOT have a negative coefficient.
 * LA var is mapped to the positive term, but both positive term and its negation are mapped to the given LVRef.
 *
 * This avoids duplicate representations and simplifies the usage of these mappings since PTRefs do not have to be
 * further normalized. The current implementation (26.5.2020) makes use of negative terms to represent all
 * possible inequalities using LEQ and negation.
 */
void LAVarMapper::registerNewMapping(LVRef lv, PTRef e_orig) {
    assert(!hasVar(e_orig));
    assert(!isNegated(e_orig));
    if (lv.x >= static_cast<unsigned int>(laVarToPTRef.size())) {
        laVarToPTRef.growTo(lv.x+1, PTRef_Undef);
    }
    laVarToPTRef[lv.x] = e_orig;

    PTId id_pos = logic.getPterm(e_orig).getId();
    PTId id_neg = logic.getPterm(logic.mkNeg(e_orig)).getId();
    assert(!hasVar(id_pos));
    int max_id = std::max(Idx(id_pos), Idx(id_neg));

    if (max_id >= ptermToLavar.size()) {
        ptermToLavar.growTo(max_id + 1, LVRef::Undef);
    }

    assert(ptermToLavar[Idx(id_pos)] == ptermToLavar[Idx(id_neg)]);
    ptermToLavar[Idx(id_pos)] = lv;
    ptermToLavar[Idx(id_neg)] = lv;
}

LVRef  LAVarMapper::getVarByPTId(PTId i) const { return ptermToLavar[Idx(i)]; }

bool LAVarMapper::hasVar(PTRef tr) const { return hasVar(logic.getPterm(tr).getId()); }

bool   LAVarMapper::hasVar(PTId i) const {
    return static_cast<unsigned int>(ptermToLavar.size()) > Idx(i) && ptermToLavar[Idx(i)] != LVRef::Undef;
}

bool LAVarMapper::isNegated(PTRef tr) const {
    if (logic.isNumConst(tr))
        return logic.getNumConst(tr) < 0; // Case (0a) and (0b)
    if (logic.isNumVar(tr))
        return false; // Case (1a)
    if (logic.isTimes(tr)) {
        // Cases (2)
        auto [v,c] = logic.splitTermToVarAndConst(tr);
        return isNegated(c);
    }
    if (logic.isIte(tr)) {
        return false;
    } else {
        // Cases(3)
        return isNegated(logic.getPterm(tr)[0]);
    }
}

void LAVarMapper::clear() {
    this->laVarToPTRef.clear();
    this->ptermToLavar.clear();
}


