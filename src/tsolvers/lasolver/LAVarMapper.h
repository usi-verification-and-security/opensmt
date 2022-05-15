/*
 *  Copyright (c) 2019-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2019-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_LAVARMAPPER_H
#define OPENSMT_LAVARMAPPER_H

#include "LARefs.h"
#include "Pterm.h"
#include "Vec.h"

class ArithLogic;


/**
 * A class for maintaining the correspondence between the Pterms and variables of the Simplex algorithm
 *
 * Variables of the Simplex algorithm, LVRefs, represent linear terms in linear arithmetic, e.g., x, x - y, -2x + 3y,
 * where x and y are variables (either of type Real or Integer).
 * Both directions of this mapping are maintained.
 *
 * In addition, a convenience mapping is maintained to obtain the corresponding LVRef directly from an inequality,
 * instead of forcing to isolate the term from the constant and normalize it.
 */
class LAVarMapper {
private:
    /** Mapping of linear Pterms to LVRefs */
    vec<LVRef>      ptermToLavar;

    /** The inverse of ptermToLavar, mapping LVRefs to PTRefs */
    vec<PTRef>      laVarToPTRef;

    ArithLogic&        logic;
public:
    LAVarMapper(ArithLogic &logic) : logic(logic) {}

    void   registerNewMapping(LVRef lv, PTRef e_orig);

    LVRef  getVarByPTId(PTId i) const;

    bool   hasVar(PTId i) const;
    bool   hasVar(PTRef tr) const;

    inline PTRef getVarPTRef(LVRef ref) const { return laVarToPTRef[ref.x]; }

    void   clear();

    bool   isNegated(PTRef tr) const;
};


#endif //OPENSMT_LAVARMAPPER_H
