//
// Created by Martin Blicha on 12.06.20.
//

#include "PTRef.h"
#include "Logic.h"

#include <unordered_map>
#include <algorithm>

#include <cassert>

#ifndef OPENSMT_MODEL_H
#define OPENSMT_MODEL_H

class Model {

public:
    using Evaluation = std::unordered_map<PTRef, PTRef, PTRefHash>;
    using SymbolDefinition = std::unordered_map<SymRef, TemplateFunction, SymRefHash>;

    Model(Logic& logic, Evaluation basicEval, SymbolDefinition symbolDef);
    Model(Logic& logic, Evaluation basicEval) : Model(logic, std::move(basicEval), {}) { }
    PTRef evaluate(PTRef term);
    TemplateFunction getDefinition(SymRef) const;
    static std::string getFormalArgBaseNameForSymbol(const Logic & logic, SymRef sr, const string & formalArgDefaultPrefix); // Return a string that is not equal to the argument

private:
    bool isCorrect(const SymbolDefinition & defs) const;
    const Evaluation varEval;
    const SymbolDefinition symDef;

    Evaluation extendedEval;

    Logic & logic;
    const std::string formalArgDefaultPrefix;

    inline bool hasVarVal(PTRef term) {
        assert(logic.isVar(term));
        return varEval.find(term) != varEval.end();
    }

    inline PTRef getVarVal(PTRef term) {
        assert(hasVarVal(term));
        return varEval.at(term);
    }

    inline bool hasDerivedVal(PTRef term) {
        return extendedEval.find(term) != extendedEval.end();
    }

    inline PTRef getDerivedVal(PTRef term) {
        assert(hasDerivedVal(term));
        return extendedEval.at(term);
    }

    inline void addDerivedVal(PTRef term, PTRef val) {
        auto res = extendedEval.insert(std::make_pair(term, val));
        assert(res.second); (void)res;
    }
};


#endif //OPENSMT_MODEL_H
