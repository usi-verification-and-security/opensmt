//
// Created by Martin Blicha on 14.06.20.
//

#include "ModelBuilder.h"

void ModelBuilder::processSubstitutions(Map<PTRef,PtAsgn,PTRefHash> const & subst) {
    Map<PTRef,PtAsgn,PTRefHash> copy;
    subst.copyTo(copy);
    logic.substitutionsTransitiveClosure(copy);
    auto assignCopy = this->assignment;
    auto model = this->build();
    auto entries = copy.getKeysAndValsPtrs();
    for (auto const * const entry : entries) {
        assert(logic.isVar(entry->key));
        if (entry->data.sgn == l_True) {
            PTRef mappedTerm = entry->data.tr;
            PTRef val = model->evaluate(mappedTerm);
            assert(logic.isConstant(val));
            assignCopy.insert(std::make_pair(entry->key, val));
        }
    }
    this->assignment = std::move(assignCopy);
}
