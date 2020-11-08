//
// Created by Martin Blicha on 12.06.20.
//

#include "Model.h"

PTRef Model::evaluate(PTRef term) {
    if (logic.isConstant(term)) {
        return term;
    }
    if (hasDerivedVal(term)) {
        return getDerivedVal(term);
    }
    if (logic.isVar(term)) {
        if (hasVarVal(term)) {
            return getVarVal(term);
        }
        // else - new variable use and remember default value
        PTRef defaultVal = logic.getDefaultValuePTRef(term);
        // cache value and return
        addDerivedVal(term, defaultVal);
        return defaultVal;
    }
    else {
        // complex term not seen before, compute and store the value
        const Pterm & t = logic.getPterm(term);
        SymRef symbol = t.symb();
        vec<PTRef> nargs;
        for (int i = 0; i < t.size(); ++i) {
            PTRef narg = evaluate(t[i]);
            nargs.push(narg);
        }
        PTRef val = logic.insertTerm(symbol, nargs);
        assert(val != PTRef_Undef);
        addDerivedVal(term, val);
        return val;
    }
}