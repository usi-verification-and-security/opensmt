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
                       [&logic](SymbolDefinition::value_type entry)
       {
           SymRef sr = entry.first;
           const Logic::TFun & templFun = entry.second;
           if (not logic.isUF(sr)) { return false; }
           const Symbol & s = logic.getSym(sr);
           if (templFun.getName().compare(logic.getSymName(sr)) != 0) { return false; }
           if (s.nargs() != templFun.getArgs().size_()) { return false; }
           if (logic.getSortRef(sr) != templFun.getRetSort()) { return false; }
           for (unsigned int i = 0; i < s.nargs(); i++)
               if (s[i] != logic.getSortRef(templFun.getArgs()[i])) return false;
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
            const Logic::TFun & tfun = symDef.at(symbol);
            const vec<PTRef> & tfunArgs = tfun.getArgs();
            Map<PTRef,PtAsgn,PTRefHash> substMap;
            for (int i = 0; i < nargs.size(); i++) {
                substMap.insert(tfunArgs[i], {nargs[i], l_True});
            }
            PTRef root = tfun.getBody();
            val = Substitutor(logic, substMap).rewrite(root);
        } else {
            val = logic.insertTerm(symbol, nargs);
        }
        assert(val != PTRef_Undef);
        addDerivedVal(term, val);
        return val;
    }
}

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

Logic::TFun Model::getDefinition(SymRef sr) const {
    if (symDef.find(sr) != symDef.end()) {
        return symDef.at(sr);
    } else {
        std::string symName = logic.getSymName(sr);
        vec<PTRef> formalArgs; formalArgs.growTo(logic.getSym(sr).nargs());
        std::string varNameBase = getFormalArgBaseNameForSymbol(logic, sr, formalArgDefaultPrefix);
        for (int i = 0; i < (int)logic.getSym(sr).nargs(); i++) {
            SRef argSort = logic.getSym(sr)[i];
            std::stringstream ss;
            ss << varNameBase << i;
            formalArgs[i] = logic.mkVar(argSort, ss.str().c_str());
        }
        return Logic::TFun(symName, formalArgs, logic.getSym(sr).rsort(), logic.getDefaultValuePTRef(logic.getSym(sr).rsort()));
    }
}