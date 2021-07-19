//
// Created by Martin Blicha on 14.06.20.
//

#include "ModelBuilder.h"

void ModelBuilder::processSubstitutions(Logic::SubstMap const & subst) {
    Logic::SubstMap copy;
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
        PTRef target = copy[key];
        PTRef mappedTerm = target;
        PTRef val = model->evaluate(mappedTerm);
        assert(logic.isConstant(val));
        assignCopy.insert(std::make_pair(key, val));
    }
    this->assignment = std::move(assignCopy);
}
