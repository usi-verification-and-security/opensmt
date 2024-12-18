/*
 * Copyright (c) 2020-2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "Model.h"

#include <algorithm>
#include <sstream>

namespace opensmt {
bool Model::isCorrect(SymbolDefinition const & defs) const {
    for (auto const & entry : defs) {
        SymRef sr = entry.first;
        TemplateFunction const & templFun = entry.second;
        if (not logic.isUF(sr)) { return false; }
        Symbol const & s = logic.getSym(sr);
        if (templFun.getName() != logic.getSymName(sr)) { return false; }
        if (s.nargs() != templFun.getArgs().size_()) { return false; }
        if (logic.getSortRef(sr) != templFun.getRetSort()) { return false; }
        for (auto i = 0; i < (int)s.nargs(); i++)
            if (s[i] != logic.getSortRef(templFun.getArgs()[i])) { return false; }
    }
    return true;
}

Model::Model(Logic & logic, Evaluation basicEval, SymbolDefinition symbolDef)
    : varEval(std::move(basicEval)),
      symDef(std::move(symbolDef)),
      logic(logic),
      formalArgDefaultPrefix("x") {
    assert(isCorrect(symbolDef));
}

PTRef Model::evaluate(PTRef term) {
    if (logic.isConstant(term)) { return term; }
    if (hasDerivedVal(term)) { return getDerivedVal(term); }
    if (logic.isVar(term)) {
        if (hasVarVal(term)) { return getVarVal(term); }
        // else - new variable use and remember default value
        PTRef defaultVal = logic.getDefaultValuePTRef(term);
        // cache value and return
        addDerivedVal(term, defaultVal);
        return defaultVal;
    } else {
        // complex term not seen before, compute and store the value
        int size = logic.getPterm(term).size();
        vec<PTRef> nargs;
        for (int i = 0; i < size; ++i) {
            PTRef narg = evaluate(logic.getPterm(term)[i]);
            nargs.push(narg);
        }
        SymRef symbol = logic.getPterm(term).symb();
        PTRef val;
        if (symDef.find(symbol) != symDef.end()) {
            TemplateFunction const & tfun = symDef.at(symbol);
            val = logic.instantiateFunctionTemplate(tfun, nargs);
        } else {
            val = logic.insertTerm(symbol, std::move(nargs));
        }
        assert(val != PTRef_Undef);
        addDerivedVal(term, val);
        return val;
    }
}

/**
 * Return a name that can be extended to a formal argument name by appending, e.g., a number.
 * The returned string is guaranteed not to collide with the name of the symbol sr after
 * appending a non-empty string
 *
 * Name collisions with sorts is possible, but should not be an issue.
 *
 * @param logic
 * @param sr
 * @param formalArgDefaultPrefix
 * @return a string that is guaranteed to be different from sr
 */
std::string Model::getFormalArgBaseNameForSymbol(Logic const & logic, SymRef sr,
                                                 std::string const & formalArgDefaultPrefix) {
    std::string const & symName(logic.getSymName(sr));

    // Collision is possible if formalArgDefaultPrefix can be extended to symName by adding at least one character.
    bool collisionPossible = formalArgDefaultPrefix == symName.substr(0, formalArgDefaultPrefix.size());

    if (collisionPossible) {
        // Modify the base by changing the first character to a different character.  Collision is then not possible
        std::string newPrefix(formalArgDefaultPrefix);
        newPrefix[0] = (symName[0] + 1) % 26 + 'a';
        assert(newPrefix[0] != symName[0]);
        return newPrefix;
    }
    return formalArgDefaultPrefix;
}

TemplateFunction Model::getDefinition(SymRef sr) const {
    if (symDef.find(sr) != symDef.end()) {
        return symDef.at(sr);
    } else {
        // A query for a function not known to egraph.  We create a default function.
        std::string symName = logic.getSymName(sr);
        vec<PTRef> formalArgs;
        formalArgs.growTo(logic.getSym(sr).nargs());
        std::string varNameBase = getFormalArgBaseNameForSymbol(logic, sr, formalArgDefaultPrefix);
        for (int i = 0; i < (int)logic.getSym(sr).nargs(); i++) {
            SRef argSort = logic.getSym(sr)[i];
            std::stringstream ss;
            ss << varNameBase << i;
            formalArgs[i] = logic.mkVar(argSort, ss.str().c_str());
        }
        return TemplateFunction(symName, formalArgs, logic.getSym(sr).rsort(),
                                logic.getDefaultValuePTRef(logic.getSym(sr).rsort()));
    }
}

std::unique_ptr<Model> Model::extend(PTRef var, PTRef val) const {
    std::array tmp{std::make_pair(var, val)};
    return extend(std::span<std::pair<PTRef, PTRef>>(tmp));
}

std::unique_ptr<Model> Model::extend(std::span<std::pair<PTRef, PTRef>> extension) const {
    auto const & base = *this;
    auto & logic = base.logic;
    assert(std::ranges::all_of(extension, [&](auto const & varVal) {
        return logic.isVar(varVal.first) and not base.hasVarVal(varVal.first);
    }));
    auto extendedEvaluation = base.varEval;
    for (auto varVal : extension) {
        extendedEvaluation.insert(varVal);
    }
    auto definitions = base.symDef;

    return std::make_unique<Model>(logic, std::move(extendedEvaluation), std::move(definitions));
}

} // namespace opensmt
