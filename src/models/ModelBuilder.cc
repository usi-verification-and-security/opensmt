//
// Created by Martin Blicha on 14.06.20.
//

#include "ModelBuilder.h"

void ModelBuilder::processSubstitutions(MapWithKeys<PTRef,PtAsgn,PTRefHash> const & subst) {
    MapWithKeys<PTRef,PtAsgn,PTRefHash> copy;
    subst.copyTo(copy);
    logic.substitutionsTransitiveClosure(copy);
    auto assignCopy = this->assignment;
    auto model = this->build();
    for (auto key : copy.getKeys()) {
        if (logic.isIte(key)) {
            // We store only values of reals variables
            continue;
        }
        assert(logic.isVar(key));
        PtAsgn target = copy[key];
        if (target.sgn == l_True) {
            PTRef mappedTerm = target.tr;
            PTRef val = model->evaluate(mappedTerm);
            assert(logic.isConstant(val));
            assignCopy.insert(std::make_pair(key, val));
        }
    }
    this->assignment = std::move(assignCopy);
}
