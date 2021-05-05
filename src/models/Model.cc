//
// Created by Martin Blicha on 12.06.20.
//

#include "Model.h"
#include "Substitutor.h"
#include <cstring>

Model::Model(Logic& logic, Evaluation basicEval, SymbolDefinition symbolDef)
    : varEval(std::move(basicEval))
    , symDef(std::move(symbolDef))
    , logic(logic)
    , formalArgDefaultPrefix("x")
{
    assert(std::all_of(symDef.begin(), symDef.end(),
                       [&logic](const SymbolDefinition::value_type & entry)
       {
           SymRef sr = entry.first;
           const TemplateFunction & templFun = entry.second;
           if (not logic.isUF(sr)) { return false; }
           const Symbol & s = logic.getSym(sr);
           if (templFun.getName() != logic.getSymName(sr)) { std::cout << "Name doesn't match" << std::endl; return false; }
           if (s.nargs() != templFun.getArgs().size_()) { std::cout << "Argument number doesn't match" << std::endl; return false; }
           if (logic.getSortRef(sr) != templFun.getRetSort()) { std::cout << "Return sorts don't match" << std::endl; return false; }
           for (auto i = 0; i < (int)s.nargs(); i++)
               if (s[i] != logic.getSortRef(templFun.getArgs()[i])) { std::cout << "argument sort doesn't match" << std::endl; return false; }
           return true;
       }));
}

PTRef Model::evaluate(PTRef term) {
    if (logic.isConstant(term)) {
        return term;
    }
    if (hasDerivedVal(term)) {
        return getDerivedVal(term);
    }
    if (logic.isVar(term)) {
        if (hasVarVal(term)) {
            return getVarVal(term);
        }
        // else - new variable use and remember default value
        PTRef defaultVal = logic.getDefaultValuePTRef(term);
        // cache value and return
        addDerivedVal(term, defaultVal);
        return defaultVal;
    }
    else {
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
            const TemplateFunction & tfun = symDef.at(symbol);
            const vec<PTRef> & tfunArgs = tfun.getArgs();
            MapWithKeys<PTRef,PTRef,PTRefHash> substMap;
            for (int i = 0; i < nargs.size(); i++) {
                substMap.insert(tfunArgs[i], nargs[i]);
            }
            PTRef root = tfun.getBody();
            val = Substitutor<PTRef>(logic, substMap).rewrite(root).first;
        } else {
            val = logic.insertTerm(symbol, nargs);
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
std::string Model::getFormalArgBaseNameForSymbol(const Logic & logic, SymRef sr, const string & formalArgDefaultPrefix) {
    const std::string & symName(logic.getSymName(sr));

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
        vec<PTRef> formalArgs; formalArgs.growTo(logic.getSym(sr).nargs());
        std::string varNameBase = getFormalArgBaseNameForSymbol(logic, sr, formalArgDefaultPrefix);
        for (int i = 0; i < (int)logic.getSym(sr).nargs(); i++) {
            SRef argSort = logic.getSym(sr)[i];
            std::stringstream ss;
            ss << varNameBase << i;
            formalArgs[i] = logic.mkVar(argSort, ss.str().c_str());
        }
        return TemplateFunction(symName, formalArgs, logic.getSym(sr).rsort(), logic.getDefaultValuePTRef(logic.getSym(sr).rsort()));
    }
}