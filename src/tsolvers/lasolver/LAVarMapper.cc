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

    PTRef neg = logic.mkNeg(e_orig);
    assert(!hasVar(e_orig));

    ptermToLavar.insert(e_orig, lv);
    ptermToLavar.insert(neg, lv);
}

LVRef LAVarMapper::getVar(PTRef term) const { assert(hasVar(term)); return ptermToLavar[term]; }

bool LAVarMapper::hasVar(PTRef tr) const { return ptermToLavar.has(tr); }

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


