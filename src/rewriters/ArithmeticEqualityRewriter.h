//
// Created by Martin Blicha on 22.02.21.
//

#ifndef OPENSMT_ARITHMETICEQUALITYREWRITER_H
#define OPENSMT_ARITHMETICEQUALITYREWRITER_H

#include "Rewriter.h"

class EqualityRewriterConfig : DefaultRewriterConfig {
    LALogic & logic;

public:
    EqualityRewriterConfig(LALogic & logic): logic(logic) {}

    bool previsit(PTRef term) override { return logic.hasSortBool(term) and not logic.isIte(term); }

    PTRef rewrite(PTRef term) override {
        if (logic.isNumEq(term)) {
            Pterm const  & p = logic.getPterm(term);
            PTRef a1 = p[0];
            PTRef a2 = p[1];
            vec<PTRef> args;
            args.push(a1); args.push(a2);
            PTRef i1 = logic.mkNumLeq(args);
            PTRef i2 = logic.mkNumGeq(args);
            logic.markSplitInequality(i1); // MB: this information should not be stored in Logic!
            logic.markSplitInequality(i2);
            args.clear();
            args.push(i1); args.push(i2);
            term = logic.mkAnd(args);
        }
        return term;
    }
};

class ArithmeticEqualityRewriter : public Rewriter<EqualityRewriterConfig> {
    EqualityRewriterConfig config;
public:
    ArithmeticEqualityRewriter(LALogic & logic): Rewriter<EqualityRewriterConfig>(logic, config), config(logic) {}
};

#endif //OPENSMT_ARITHMETICEQUALITYREWRITER_H
