/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_EGRAPHMODELBUILDER_H
#define OPENSMT_EGRAPHMODELBUILDER_H

#include "Egraph.h"

namespace opensmt {

class EgraphModelBuilder {
    Logic & logic;
    Egraph::Values & values;
    EnodeStore const & enode_store;
    Map<ERef, PTRef, ERefHash> rootValues;

public:
    EgraphModelBuilder(Egraph const & owner) : logic(owner.logic), values(*owner.values), enode_store(owner.enode_store) {}

    void fill(ModelBuilder & modelBuilder) &&;

private:
    bool hasArithmetic() const { return logic.hasIntegers() or logic.hasReals(); }

    void addTheoryFunctionEvaluation(ModelBuilder & modelBuilder, PTRef tr, ERef er);

    Map<ERef, PTRef, ERefHash> computeNumericValues (ModelBuilder const &) const;

    PTRef getAbstractValueForERef (ERef er, SRef sr);

    Enode const & getEnode(ERef ref) const { return enode_store[ref]; }

};

}

#endif //OPENSMT_EGRAPHMODELBUILDER_H
