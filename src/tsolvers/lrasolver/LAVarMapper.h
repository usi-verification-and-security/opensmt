//
// Created by prova on 06.09.19.
//

#ifndef OPENSMT_LAVARMAPPER_H
#define OPENSMT_LAVARMAPPER_H

#include "LAVar.h"

class LAVarMapper {
private:
    LAVarStore&     laVarStore;
    vec<LVRef>      leqToLavar;              // Maps Pterm constraints to solver's real variables.
    vec<LVRef>      ptermToLavar;            // Maps Pterm variables to solver's real variables
    vec<PTRef>      laVarToPTRef;
    LALogic&        logic;
public:
    LAVarMapper(LALogic &logic, LAVarStore &store) : laVarStore(store), logic(logic) {}
    LVRef  getNewVar(PTRef e_orig);
    LVRef  getVarByPTId(PTId i) const;
    void   addLeqVar(PTRef leq_tr, LVRef v); // Adds a binding from leq_tr to the "slack var" v
    LVRef  getVarByLeqId(PTId i) const;
    bool   hasVar(PTId i) ;
    bool   hasVar(PTRef tr);
    inline PTRef getVarPTRef(LVRef ref) const { return laVarToPTRef[ref.x]; }
    unsigned numVars() const { return laVarStore.numVars(); }
};


#endif //OPENSMT_LAVARMAPPER_H
