#include "UFLRATheory.h"
#include "OsmtInternalException.h"
#include "TreeOps.h"
#include "Substitutor.h"
#include "ArithmeticEqualityRewriter.h"

bool UFLRATheory::simplify(const vec<PFRef>& formulas, PartitionManager &pmanager, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    if (this->keepPartitions()) {
        throw OsmtInternalException("Mode not supported for QF_UFLRA yet");
    } else {
        PTRef fla = logic.mkAnd(currentFrame.formulas);
        PTRef purified = purify(fla);
        PTRef noArithmeticEqualities = splitArithmeticEqualities(purified);
        PTRef enriched = addInterfaceClauses(noArithmeticEqualities);
        currentFrame.root = enriched;
    }
    return true;
}

namespace {
    bool isArithmeticSymbol(ArithLogic const & logic, SymRef sym) {
        return logic.isTheorySymbol(sym) and logic.getSym(sym).isInterpreted();
    }

    bool isUninterpreted(ArithLogic const & logic, SymRef sym) {
        return logic.isUF(sym) and logic.getSym(sym).nargs() > 0;
    }


    class PurifyConfig : public DefaultVisitorConfig {
        static std::string prefix;
        ArithLogic & logic;
        Logic::SubstMap substMap;

        void createVarFor(PTRef ptref) {
            if (substMap.has(ptref)) {
                return;
            }
            assert(logic.yieldsSortNum(ptref));
            auto name = prefix + std::to_string(ptref.x);
            PTRef var = logic.mkVar(logic.getSortRef(ptref), name.c_str());
            substMap.insert(ptref, var);
        }

    public:
        PurifyConfig(ArithLogic & logic) : DefaultVisitorConfig(), logic(logic) {}

        void visit(PTRef ptref) override {
            auto const & term = logic.getPterm(ptref);
            if (isArithmeticSymbol(logic, term.symb())) {
                auto nargs = term.nargs();
                for (unsigned i = 0; i < nargs; ++i) {
                    PTRef child = logic.getPterm(ptref)[i];
                    if (isUninterpreted(logic, logic.getSymRef(child))) {
                        createVarFor(child);
                    }
                }
            }
        }

        Logic::SubstMap const & getPurificationMap() const { return substMap; }
    };

    std::string PurifyConfig::prefix = ".purify_";

    class Purifier : public TermVisitor<PurifyConfig> {
        PurifyConfig config;

    public:
        Purifier(ArithLogic & logic) : TermVisitor<PurifyConfig>(logic, config), config(logic) {}

        Logic::SubstMap const & getPurificationMap() const { return config.getPurificationMap(); }
    };
}

PTRef UFLRATheory::purify(PTRef fla) {
    Purifier purifier(getLogic());
    purifier.visit(fla);
    auto const & renameMap = purifier.getPurificationMap();
    vec<PTRef> equalities;
    equalities.capacity(renameMap.getSize() + 1);
    for (PTRef key : renameMap.getKeys()) {
        equalities.push(logic.mkEq(key, renameMap[key]));
    }
    equalities.push(Substitutor(logic, renameMap).rewrite(fla));
    return logic.mkAnd(equalities);
}

bool UFLRATheory::containsUF(PTRef term) const {
    class UFFinderConfig : public DefaultVisitorConfig {
        ArithLogic & logic;
    public:
        UFFinderConfig(ArithLogic & logic) : DefaultVisitorConfig(), logic(logic) {}
        bool previsit(PTRef term) override { return not ufFound; }

        void visit(PTRef term) override {
            if (isUninterpreted(logic, logic.getSymRef(term))) {
                ufFound = true;
            }
        }

        bool ufFound = false;
    } config(logic);
    TermVisitor<UFFinderConfig>(logic, config).visit(term);
    return config.ufFound;
}

template<typename Pred>
class RewriterConfig : public DefaultRewriterConfig {
    ArithLogic & logic;
    Pred pred;
public:
    RewriterConfig(ArithLogic & logic, Pred pred) : logic(logic), pred(pred) {}

    bool previsit(PTRef term) override { return logic.hasSortBool(term) and not logic.isIte(term); }

    PTRef rewrite(PTRef term) override {
        if (logic.isNumEq(term) && pred(term)) {
            Pterm const  & p = logic.getPterm(term);
            PTRef a1 = p[0];
            PTRef a2 = p[1];
            PTRef i1 = logic.mkLeq(a1, a2);
            PTRef i2 = logic.mkGeq(a1, a2);
            return logic.mkAnd(i1, i2);
        }
        return term;
    }
};

PTRef UFLRATheory::splitArithmeticEqualities(PTRef fla) {
    auto split = [this](PTRef term) { return not this->containsUF(term); };
    auto config = RewriterConfig(logic, split);
    auto rewriter = Rewriter(logic, config);
    return rewriter.rewrite(fla);
}

class CollectEqsConfig : public DefaultVisitorConfig {
    vec<PTRef> eqs;
    ArithLogic & logic;

public:
    CollectEqsConfig(ArithLogic & logic) : DefaultVisitorConfig(), logic(logic) {}

    bool previsit(PTRef ptref) override {
        return logic.hasSortBool(ptref);
    }

    void visit(PTRef ptref) override {
        if (logic.isEquality(ptref)) {
            eqs.push(ptref);
        }
    }

    vec<PTRef> const & getEqs() const { return eqs; }
};

PTRef UFLRATheory::addInterfaceClauses(PTRef fla) {
    if (not logic.isAnd(fla)) { return fla; }
    vec<PTRef> interfaceVars;
    CollectEqsConfig config(logic);
    TermVisitor(logic, config).visit(fla);
    for (PTRef eq : config.getEqs()) {
        MapWithKeys<PTRef,bool,PTRefHash> allVars;
        getVars(eq, logic, allVars);
        for (PTRef var : allVars.getKeys()) {
            if (logic.isNumVar(var)) {
                if (std::find(interfaceVars.begin(), interfaceVars.end(), var) == interfaceVars.end()) {
                    interfaceVars.push(var);
                }
            }
        }
    }
    // Add all interface clauses to the formula
    vec<PTRef> interfaceClauses;
    for (int i = 0; i < interfaceVars.size(); ++i) {
        for (int j = 0; j < i; ++j) {
            PTRef lhs = interfaceVars[i];
            PTRef rhs = interfaceVars[j];
            PTRef eq = logic.mkEq(lhs, rhs);
            PTRef leq = logic.mkLeq(lhs, rhs);
            PTRef geq = logic.mkGeq(lhs, rhs);
            // x = y <=> x <= y && x >= y
            interfaceClauses.push(logic.mkOr({logic.mkNot(eq), leq}));
            interfaceClauses.push(logic.mkOr({logic.mkNot(eq), geq}));
            interfaceClauses.push(logic.mkOr({logic.mkNot(leq), logic.mkNot(geq), eq}));
        }
    }
    interfaceClauses.push(fla);
    return logic.mkAnd(std::move(interfaceClauses));
}