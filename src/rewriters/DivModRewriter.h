/*
 * Copyright (c) 2021-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_DIVMODREWRITER_H
#define OPENSMT_DIVMODREWRITER_H

#include "Rewriter.h"

#include "ArithLogic.h"
#include "PTRef.h"

#include "OsmtApiException.h"
#include "OsmtInternalException.h"
#include "TypeUtils.h"

#include <string>
#include <unordered_map>

class DivModConfig : public DefaultRewriterConfig {
    ArithLogic & logic;

    struct DivModPair {
        PTRef div;
        PTRef mod;
    };

    std::unordered_map<std::pair<PTRef, PTRef>, DivModPair, PTRefPairHash> divModCache;
    vec<PTRef> definitions;

    DivModPair freshDivModPair(PTRef dividend, PTRef divisor) {
        std::string id = "_" + std::to_string(dividend.x) + "_" + std::to_string(divisor.x);
        std::string divName(divPrefix);
        divName += id;
        std::string modName(modPrefix);
        modName += id;
        return {logic.mkIntVar(divName.c_str()), logic.mkIntVar(modName.c_str())};
    }

    static opensmt::pair<PTRef, PTRef> getDividendAndDivisor(std::string_view const name,
                                                             std::string_view const prefix) {
        std::string dividendNumberStr;
        std::string divisorNumberStr;
        bool parsingDividend = true;
        for (auto it = name.begin() + prefix.size() + 1; it != name.end(); ++it) {
            if (parsingDividend and '0' <= *it and *it <= '9') {
                dividendNumberStr += *it;
            } else if (not parsingDividend and '0' <= *it and *it <= '9') {
                divisorNumberStr += *it;
            } else if (*it == '_') {
                if (not parsingDividend)
                    throw OsmtInternalException("Parse error in auxiliary variable symbol: " + std::string(name));
                parsingDividend = false;
            }
        }
        return {{static_cast<uint32_t>(std::stoul(dividendNumberStr))},
                {static_cast<uint32_t>(std::stoul(divisorNumberStr))}};
    }

public:
    static std::string_view constexpr divPrefix = ".div";
    static std::string_view constexpr modPrefix = ".mod";

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
            if (not inCache) { divModCache.insert({{dividend, divisor}, divMod}); }
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
                definitions.push(logic.mkAnd(logic.mkEq(dividend, logic.mkPlus(logic.mkTimes(divisor, divVar), modVar)),
                                             logic.mkAnd(logic.mkLeq(logic.getTerm_IntZero(), modVar),
                                                         logic.mkLeq(modVar, logic.mkIntConst(upperBound)))));
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

    // Inverse operator from auxVar to Div Term
    static PTRef getDivTermFor(ArithLogic & logic, PTRef auxVar) {
        std::string const & name = logic.getSymName(auxVar);
        assert(name.compare(0, divPrefix.size(), divPrefix) == 0);
        auto [dividendTr, divisorTr] = getDividendAndDivisor(name, divPrefix);
        return logic.mkIntDiv(dividendTr, divisorTr);
    }

    // Inverse operator from auxVar to Mod Term
    static PTRef getModTermFor(ArithLogic & logic, PTRef auxVar) {
        std::string const & name = logic.getSymName(auxVar);
        assert(name.compare(0, modPrefix.size(), modPrefix) == 0);
        auto [dividendTr, divisorTr] = getDividendAndDivisor(name, modPrefix);
        return logic.mkMod(dividendTr, divisorTr);
    }
};

class DivModRewriter : Rewriter<DivModConfig> {
    ArithLogic & logic;
    DivModConfig config;

public:
    DivModRewriter(ArithLogic & logic) : Rewriter<DivModConfig>(logic, config), logic(logic), config(logic) {}

    PTRef rewrite(PTRef term) override {
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
inline PTRef rewriteDivMod(ArithLogic & logic, PTRef root) { return DivModRewriter(logic).rewrite(root); }

#endif // OPENSMT_DIVMODEREWRITER_H
