//
// Created by Martin Blicha on 22.02.21.
//

#ifndef OPENSMT_ARITHMETICEQUALITYREWRITER_H
#define OPENSMT_ARITHMETICEQUALITYREWRITER_H

#include "Rewriter.h"

class EqualityRewriterConfig : DefaultRewriterConfig {
    std::unique_ptr<Map<PTRef,bool,PTRefHash>> notOkToPartition;
    LALogic & logic;
public:
    EqualityRewriterConfig(LALogic & logic): logic(logic) { notOkToPartition = std::unique_ptr<Map<PTRef,bool,PTRefHash>>(new Map<PTRef,bool,PTRefHash>()); }

    std::unique_ptr<Map<PTRef,bool,PTRefHash>> getAndClearNotOkToPartition() {
        auto tmp = std::unique_ptr<Map<PTRef,bool,PTRefHash>>(new Map<PTRef,bool,PTRefHash>());
        std::swap(tmp, notOkToPartition); return tmp;
    }

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
            notOkToPartition->insert(i1, true);
            notOkToPartition->insert(i2, true);
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
    std::unique_ptr<Map<PTRef,bool,PTRefHash>> getAndClearNotOkToPartition() { return config.getAndClearNotOkToPartition(); }
};


#endif //OPENSMT_ARITHMETICEQUALITYREWRITER_H
