//
// Created by Antti on 09.08.21.
//

#ifndef OPENSMT_ABSREWRITER_H
#define OPENSMT_ABSREWRITER_H
#include "PTRef.h"

#include "Rewriter.h"
#include "ArithLogic.h"

#include "OsmtApiException.h"

#include <unordered_map>
#include <string>

class AbsConfig : public DefaultRewriterConfig {
    ArithLogic & logic;

    std::unordered_map<PTRef, PTRef, PTRefHash> absCache;
    vec<PTRef> definitions;

    const char * absPrefix = ".abs";

    PTRef freshAbs(PTRef abs) {
        std::string id = std::string(absPrefix) + "_" + std::to_string(abs.x);
        return logic.mkNumVar(id.c_str());
    }

public:
    AbsConfig(ArithLogic & logic) : logic(logic) {}

    PTRef rewrite(PTRef term) override {
        SymRef symRef = logic.getSymRef(term);
        if (logic.isNumAbs(symRef)) {
            assert(logic.getPterm(term).size() == 1);
            auto it = absCache.find(term);
            bool inCache = (it != absCache.end());
            PTRef rewritten = inCache ? it->second : freshAbs(term);
            if (not inCache) {
                definitions.push(logic.mkEq(term, logic.mkIte(logic.mkNumGeq(term, logic.getTerm_NumZero()), term, logic.mkNumNeg(term))));
            }
            return rewritten;
        }
        return term;
    }

    void getDefinitions(vec<PTRef> & out) {
        for (PTRef def : definitions) {
            out.push(def);
        }
    }
};

class AbsRewriter : Rewriter<AbsConfig> {
    ArithLogic & logic;
    AbsConfig config;
public:
    AbsRewriter(ArithLogic & logic) : Rewriter<AbsConfig>(logic, config), logic(logic), config(logic) {}

    PTRef rewrite(PTRef term) {
        if (term == PTRef_Undef or logic.hasSortNum(term)) {
            throw OsmtApiException("Abs rewriting should only be called on formulas, not terms!");
        }
        PTRef rewritten = Rewriter<AbsConfig>::rewrite(term);
        vec<PTRef> args;
        args.push(rewritten);
        config.getDefinitions(args);
        return logic.mkAnd(args);
    }
};

#endif //OPENSMT_ABSREWRITER_H
