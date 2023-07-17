/*
 * Copyright (c) 2021-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_ARITHMETICEQUALITYREWRITER_H
#define OPENSMT_ARITHMETICEQUALITYREWRITER_H

#include "Rewriter.h"

class EqualityRewriterConfig : public DefaultRewriterConfig {
    ArithLogic & logic;
    std::unique_ptr<Map<PTRef, bool, PTRefHash>> notOkToPartition;

public:
    EqualityRewriterConfig(ArithLogic & logic) : logic(logic), notOkToPartition(new Map<PTRef, bool, PTRefHash>()) {}

    std::unique_ptr<Map<PTRef, bool, PTRefHash>> getAndClearNotOkToPartition() {
        return std::exchange(notOkToPartition, std::make_unique<Map<PTRef, bool, PTRefHash>>());
    }

    bool previsit(PTRef term) override { return logic.hasSortBool(term) and not logic.isIte(term); }

    PTRef rewrite(PTRef term) override {
        if (logic.isNumEq(term)) {
            Pterm const & p = logic.getPterm(term);
            PTRef a1 = p[0];
            PTRef a2 = p[1];
            PTRef i1 = logic.mkLeq(a1, a2);
            PTRef i2 = logic.mkGeq(a1, a2);
            notOkToPartition->insert(i1, true);
            notOkToPartition->insert(i2, true);
            term = logic.mkAnd(i1, i2);
        }
        return term;
    }
};

class ArithmeticEqualityRewriter : public Rewriter<EqualityRewriterConfig> {
    EqualityRewriterConfig config;

public:
    explicit ArithmeticEqualityRewriter(ArithLogic & logic)
        : Rewriter<EqualityRewriterConfig>(logic, config), config(logic) {}
    std::unique_ptr<Map<PTRef, bool, PTRefHash>> getAndClearNotOkToPartition() {
        return config.getAndClearNotOkToPartition();
    }
};

#endif // OPENSMT_ARITHMETICEQUALITYREWRITER_H
