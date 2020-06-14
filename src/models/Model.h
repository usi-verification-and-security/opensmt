//
// Created by Martin Blicha on 12.06.20.
//

#include "PTRef.h"
#include "Logic.h"

#include <unordered_map>

#ifndef OPENSMT_MODEL_H
#define OPENSMT_MODEL_H


class Model {

public:
    using Evaluation = std::unordered_map<PTRef, PTRef, PTRefHash>;


    Model(Logic& logic, Evaluation basicEval) : varEval{basicEval}, logic{logic} {}

    PTRef evaluate(PTRef term);

private:
    const Evaluation varEval;

    Evaluation extendedEval;

    Logic & logic;

    // helper methods
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
