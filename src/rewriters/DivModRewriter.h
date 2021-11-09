//
// Created by Martin Blicha on 03.02.21.
//

#ifndef OPENSMT_DIVMODREWRITER_H
#define OPENSMT_DIVMODREWRITER_H

#include "PTRef.h"

#include "Rewriter.h"
#include "ArithLogic.h"

#include "OsmtApiException.h"

#include <unordered_map>
#include <string>

class DivModConfig : public DefaultRewriterConfig {
    ArithLogic & logic;

    struct DivModPair {
        PTRef div;
        PTRef mod;
    };

    std::unordered_map<std::pair<PTRef, PTRef>, DivModPair, PTRefPairHash> divModCache;
    vec<PTRef> definitions;

    const char * divPrefix = ".div";
    const char * modPrefix = ".mod";

    DivModPair freshDivModPair(PTRef dividend, PTRef divisor) {
        std::string id = "_" + std::to_string(dividend.x) + "_" + std::to_string(divisor.x);
        std::string divName = divPrefix + id;
        std::string modName = modPrefix + id;
        return {logic.mkIntVar(divName.c_str()), logic.mkIntVar(modName.c_str())};
    }

public:
    DivModConfig(ArithLogic & logic) : logic(logic) {}

    PTRef rewrite(PTRef term) override {
        SymRef symRef = logic.getSymRef(term);
        if (logic.isIntDiv(symRef) || logic.isMod(symRef)) {
            assert(logic.getPterm(term).size() == 2);
            PTRef dividend = logic.getPterm(term)[0];
            PTRef divisor = logic.getPterm(term)[1];
            // check cache first
            auto it = divModCache.find({dividend, divisor});
            bool inCache = (it != divModCache.end());
            DivModPair divMod = inCache ? it->second : freshDivModPair(dividend, divisor);
            if (not inCache) {
                divModCache.insert({{dividend, divisor}, divMod});
            }
            PTRef divVar = divMod.div;
            PTRef modVar = divMod.mod;
            PTRef rewritten = logic.isIntDiv(symRef) ? divVar : modVar;
            if (not inCache) {
                // collect the definitions to add
                assert(logic.isConstant(divisor));
                auto divisorVal = logic.getNumConst(divisor);
                // general case
                auto upperBound = abs(divisorVal) - 1;
                // dividend = divVar * divisor + modVar
                // 0 <= modVar <= |dividend| - 1
                definitions.push(logic.mkAnd(
                        logic.mkEq(dividend, logic.mkPlus(logic.mkTimes(divisor, divVar), modVar)),
                        logic.mkAnd(
                                logic.mkLeq(logic.getTerm_IntZero(), modVar),
                                logic.mkLeq(modVar, logic.mkIntConst(upperBound))
                        )
                ));
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

class DivModRewriter : Rewriter<DivModConfig> {
    ArithLogic & logic;
    DivModConfig config;
public:
    DivModRewriter(ArithLogic & logic) : Rewriter<DivModConfig>(logic, config), logic(logic), config(logic) {}

    PTRef rewrite(PTRef term) {
        if (term == PTRef_Undef or not logic.hasSortBool(term)) {
            throw OsmtApiException("Div/Mod rewriting should only be called on formulas, not terms!");
        }
        PTRef rewritten = Rewriter<DivModConfig>::rewrite(term);
        vec<PTRef> args;
        args.push(rewritten);
        config.getDefinitions(args);
        return logic.mkAnd(args);
    }
};

// Simple single-use version
inline PTRef rewriteDivMod(ArithLogic & logic, PTRef root) {
    return DivModRewriter(logic).rewrite(root);
}


#endif //OPENSMT_DIVMODEREWRITER_H
