//
// Created by Martin Blicha on 03.02.21.
//

#ifndef OPENSMT_DIVMODREWRITER_H
#define OPENSMT_DIVMODREWRITER_H
#endif

#include "PTRef.h"

#include "Rewriter.h"
#include "ArithLogic.h"

#include "OsmtApiException.h"

#include <unordered_map>
#include <string>

class CounterConfig : public DefaultRewriterConfig {
    Logic & logic;

    vec<PTRef> definitions;

public:
    int varNumber;
    int boolNumber;
    CounterConfig(Logic & logic) : logic(logic) {
        varNumber = 0;
        boolNumber = 0;
    }

    PTRef rewrite(PTRef term) override {
        SymRef symRef = logic.getSymRef(term);
        if (logic.isVar(symRef)) {
            varNumber++;
        } else if (logic.isBooleanOperator(symRef)) {
            boolNumber++;
        }
        return term;
    }

    void getDefinitions(vec<PTRef> & out) {
        for (PTRef def : definitions) {
            out.push(def);
        }
    }
};

class CounterRewriter : Rewriter<CounterConfig> {
    Logic & logic;
public:
    CounterConfig config;
    CounterRewriter(Logic & logic) : Rewriter<CounterConfig>(logic, config), logic(logic), config(logic) {}

    PTRef rewrite(PTRef term) {
        PTRef rewritten = Rewriter<CounterConfig>::rewrite(term);
        vec<PTRef> args;
        args.push(rewritten);
        config.getDefinitions(args);
        return logic.mkAnd(args);
    }
};

// Simple single-use version
inline PTRef rewriteCounter(Logic & logic, PTRef root) {
    return CounterRewriter(logic).rewrite(root);
}


//OPENSMT_DIVMODEREWRITER_H
