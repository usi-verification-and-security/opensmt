//
// Created by prova on 06.09.19.
//

#ifndef OPENSMT_LAVARMAPPER_H
#define OPENSMT_LAVARMAPPER_H

#include "LARefs.h"
#include "Pterm.h"
#include "Vec.h"

class LALogic;


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
    /** Convenience mapping of inequalities to LVRef representing the linear term without constant in the inequality*/
    vec<LVRef>      leqToLavar;

    /** Mapping of linear Pterms to LVRefs */
    vec<LVRef>      ptermToLavar;

    /** The inverse of ptermToLavar, mapping LVRefs to PTRefs */
    vec<PTRef>      laVarToPTRef;

    LALogic&        logic;
public:
    LAVarMapper(LALogic &logic) : logic(logic) {}

    void   registerNewMapping(LVRef lv, PTRef e_orig);

    void   addLeqVar(PTRef leq_tr, LVRef v); // Adds a binding from leq_tr to the "slack var" v

    LVRef  getVarByPTId(PTId i) const;
    LVRef  getVarByLeqId(PTId i) const;

    bool   hasVar(PTId i) const;
    bool   hasVar(PTRef tr) const;

    inline PTRef getVarPTRef(LVRef ref) const { return laVarToPTRef[ref.x]; }

    void   clear();

};


#endif //OPENSMT_LAVARMAPPER_H
