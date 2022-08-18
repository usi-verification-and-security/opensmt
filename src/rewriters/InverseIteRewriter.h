//
// Created by prova on 18.08.22.
//

#ifndef OPENSMT_INVERSEITEREWRITER_H
#define OPENSMT_INVERSEITEREWRITER_H

#include "Logic.h"
#include "IteHandler.h"
#include "TreeOps.h"
#include "Rewriter.h"
#include "OsmtInternalException.h"

class InverseIteRewriter {
    class AuxIteSymbolMatcher {
        Logic const & logic;
    public:
        AuxIteSymbolMatcher(Logic const & logic) : logic(logic) {}
        bool operator () (PTRef tr) { return std::string(logic.getSymName(tr)).compare(0, IteHandler::itePrefix.size(), IteHandler::itePrefix) == 0; }
    };

    class IteRewriterConfig : public DefaultRewriterConfig {
        Logic const & logic;
        std::unordered_set<PTRef> auxIteTerms;

    public:
        IteRewriterConfig(Logic const & logic, vec<PTRef> const & auxIteTerms) : logic(logic), auxIteTerms(auxIteTerms.begin(), auxIteTerms.end(), 10) {}
        PTRef rewrite(PTRef term) override {
            return (auxIteTerms.find(term) != auxIteTerms.end()) ? IteHandler::getIteTermFor(logic, term) : term;
        }
    };
    Logic & logic;
public:
    InverseIteRewriter(Logic & logic) : logic(logic) {}
    PTRef rewrite(PTRef root) {
        auto auxIteSymbolMatcherConfig = TermCollectorConfig(AuxIteSymbolMatcher(logic));
        TermVisitor(logic, auxIteSymbolMatcherConfig).visit(root);
        auto rewriterConfig = IteRewriterConfig(logic, auxIteSymbolMatcherConfig.extractCollectedTerms());
        PTRef rootWithItes = Rewriter(logic, rewriterConfig).rewrite(root);
        assert([this](PTRef rootWithItes) {
            auto tmpConfig = TermCollectorConfig(AuxIteSymbolMatcher(logic));
            TermVisitor(logic, tmpConfig).visit(rootWithItes);
            bool ok = (tmpConfig.extractCollectedTerms().size() == 0);
            if (not ok) {
                throw OsmtInternalException("Rewritten root contains Ites");
            }
            return ok;
        }(rootWithItes));
        return rootWithItes;
    }
};


#endif //OPENSMT_INVERSEITEREWRITER_H
