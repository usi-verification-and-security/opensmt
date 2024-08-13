//
// Created by Martin Blicha on 12.06.20.
//

#include <logics/Logic.h>
#include <pterms/PTRef.h>

#include <algorithm>
#include <cassert>
#include <unordered_map>

#ifndef OPENSMT_MODEL_H
#define OPENSMT_MODEL_H

namespace opensmt {
class Model {
public:
    using Evaluation = std::unordered_map<PTRef, PTRef, PTRefHash>;
    using SymbolDefinition = std::unordered_map<SymRef, TemplateFunction, SymRefHash>;

    Model(Logic & logic, Evaluation basicEval, SymbolDefinition symbolDef);
    Model(Logic & logic, Evaluation basicEval) : Model(logic, std::move(basicEval), {}) {}
    PTRef evaluate(PTRef term);
    TemplateFunction getDefinition(SymRef) const;
    static std::string getFormalArgBaseNameForSymbol(
        Logic const & logic, SymRef sr,
        std::string const & formalArgDefaultPrefix); // Return a string that is not equal to the argument

private:
    bool isCorrect(SymbolDefinition const & defs) const;
    Evaluation const varEval;
    SymbolDefinition const symDef;

    Evaluation extendedEval;

    Logic & logic;
    std::string const formalArgDefaultPrefix;

    inline bool hasVarVal(PTRef term) const {
        assert(logic.isVar(term));
        return varEval.find(term) != varEval.end();
    }

    inline PTRef getVarVal(PTRef term) const {
        assert(hasVarVal(term));
        return varEval.at(term);
    }

    inline bool hasDerivedVal(PTRef term) { return extendedEval.find(term) != extendedEval.end(); }

    inline PTRef getDerivedVal(PTRef term) {
        assert(hasDerivedVal(term));
        return extendedEval.at(term);
    }

    inline void addDerivedVal(PTRef term, PTRef val) {
        auto res = extendedEval.insert(std::make_pair(term, val));
        assert(res.second);
        (void)res;
    }
};
} // namespace opensmt

#endif // OPENSMT_MODEL_H
