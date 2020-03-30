//
// Created by prova on 06.09.19.
//

#ifndef OPENSMT_LAVARMAPPER_H
#define OPENSMT_LAVARMAPPER_H

#include "LARefs.h"
#include "Pterm.h"
#include "Vec.h"

class LALogic;


class LAVarMapper {
private:
    vec<LVRef>      leqToLavar;              // Maps Pterm constraints to solver's real variables.
    vec<LVRef>      ptermToLavar;            // Maps Pterm variables to solver's real variables
    vec<PTRef>      laVarToPTRef;
    LALogic&        logic;
public:
    LAVarMapper(LALogic &logic) : logic(logic) {}
    LVRef  registerNewMapping(LVRef v, PTRef e_orig);
    LVRef  getVarByPTId(PTId i) const;
    void   addLeqVar(PTRef leq_tr, LVRef v); // Adds a binding from leq_tr to the "slack var" v
    LVRef  getVarByLeqId(PTId i) const;
    bool   hasVar(PTId i) ;
    bool   hasVar(PTRef tr);
    void   clear();
    inline PTRef getVarPTRef(LVRef ref) const { return laVarToPTRef[ref.x]; }

};


#endif //OPENSMT_LAVARMAPPER_H
