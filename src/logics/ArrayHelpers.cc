/*
 *  Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "ArrayHelpers.h"

#include <common/TreeOps.h>

namespace opensmt {

vec<PTRef> collectStores(Logic const & logic, PTRef fla) {
    class CollectStoresConfig : public DefaultVisitorConfig {
        Logic const & logic;

    public:
        vec<PTRef> stores;

        CollectStoresConfig(Logic const & logic) : logic(logic) {}

        void visit(PTRef term) override {
            if (logic.isArrayStore(term)) {
                stores.push(term);
            }
        }
    };

    CollectStoresConfig config(logic);
    TermVisitor<CollectStoresConfig> visitor(logic, config);
    visitor.visit(fla);
    return std::move(config.stores);
}

PTRef instantiateReadOverStore(Logic & logic, PTRef fla) {
    vec<PTRef> stores = collectStores(logic, fla);
    vec<PTRef> instantiatedAxioms;
    for (PTRef store : stores) {
        PTRef index = logic.getPterm(store)[1];
        PTRef value = logic.getPterm(store)[2];
        assert(logic.isArrayStore(store));
        instantiatedAxioms.push(logic.mkEq(logic.mkSelect({store, index}), value));
    }
    instantiatedAxioms.push(fla);
    return logic.mkAnd(std::move(instantiatedAxioms));
}

}
