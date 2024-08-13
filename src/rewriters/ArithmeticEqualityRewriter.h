/*
 * Copyright (c) 2021-2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_ARITHMETICEQUALITYREWRITER_H
#define OPENSMT_ARITHMETICEQUALITYREWRITER_H

#include "Rewriter.h"

#include <logics/ArithLogic.h>

namespace opensmt {
class EqualityRewriterConfig : public DefaultRewriterConfig {
public:
    explicit EqualityRewriterConfig(ArithLogic & logic) : logic(logic) {}

    bool previsit(PTRef term) override { return logic.hasSortBool(term) and not logic.isIte(term); }

    PTRef rewrite(PTRef term) override {
        if (logic.isNumEq(term)) {
            Pterm const & p = logic.getPterm(term);
            PTRef a1 = p[0];
            PTRef a2 = p[1];
            PTRef i1 = logic.mkLeq(a1, a2);
            PTRef i2 = logic.mkGeq(a1, a2);
            term = logic.mkAnd(i1, i2);
        }
        return term;
    }

private:
    ArithLogic & logic;
};

class ArithmeticEqualityRewriter : public Rewriter<EqualityRewriterConfig> {
public:
    explicit ArithmeticEqualityRewriter(ArithLogic & logic)
        : Rewriter<EqualityRewriterConfig>(logic, config),
          config(logic) {}

private:
    EqualityRewriterConfig config;
};
} // namespace opensmt

#endif // OPENSMT_ARITHMETICEQUALITYREWRITER_H
