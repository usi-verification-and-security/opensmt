#include "UFLATheory.h"
#include "OsmtInternalException.h"
#include "TreeOps.h"
#include "Substitutor.h"
#include "ArithmeticEqualityRewriter.h"

bool UFLATheory::simplify(const vec<PFRef>& formulas, PartitionManager &pmanager, int curr)
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
        return logic.isIF(sym) and not logic.isEquality(sym) and not logic.isBooleanOperator(sym);
    }

    bool isUninterpreted(ArithLogic const & logic, SymRef sym) {
        return logic.isUF(sym);
    }

    /*
     * Helper function to determine if an arithmetic equality is pure or not
     * // NOTE: This is correct only under the condition that children have been purified
     */
    bool isPureArithmeticEquality(PTRef ptref, ArithLogic & logic) {
        assert(logic.isNumEq(ptref));
        auto const & term = logic.getPterm(ptref);
        PTRef lhs = term[0];
        PTRef rhs = term[1];
        return not (isUninterpreted(logic, logic.getSymRef(lhs)) or isUninterpreted(logic, logic.getSymRef(rhs)));
    }

    class PurifyConfig : public DefaultRewriterConfig {
        static constexpr const char * prefix = ".purify_";
        ArithLogic & logic;
        Logic::SubstMap freshVarMap;
        vec<PTRef> auxArgs;

        void createVarFor(PTRef ptref) {
            if (freshVarMap.has(ptref)) {
                return;
            }
            assert(logic.yieldsSortNum(ptref));
            auto name = prefix + std::to_string(ptref.x);
            PTRef var = logic.mkVar(logic.getSortRef(ptref), name.c_str());
            freshVarMap.insert(ptref, var);
        }

        template<typename TIsInterestingChild>
        PTRef rewriteInternal(PTRef ptref, TIsInterestingChild && isInteresting) {
            auxArgs.clear();
            bool needsRewriting = false;
            auto nargs = logic.getPterm(ptref).nargs();
            for (unsigned i = 0; i < nargs; ++i) {
                PTRef child = logic.getPterm(ptref)[i];
                if (isInteresting(child)) {
                    createVarFor(child);
                    auxArgs.push(freshVarMap[child]);
                    needsRewriting = true;
                } else {
                    auxArgs.push(child);
                }
            }
            return needsRewriting ? logic.insertTerm(logic.getPterm(ptref).symb(), std::move(auxArgs)) : ptref;
        }

    public:
        PurifyConfig(ArithLogic & logic) : DefaultRewriterConfig(),
            logic(logic) {
        }

        PTRef rewrite(PTRef ptref) override {
            auto const & term = logic.getPterm(ptref);
            if (isArithmeticSymbol(logic, term.symb())) {
                return rewriteInternal(ptref, [this](PTRef child) { return isUninterpreted(logic, logic.getSymRef(child)); });
            } else if (isUninterpreted(logic, term.symb())) {
                return rewriteInternal(ptref, [this](PTRef child) { return isArithmeticSymbol(logic, logic.getSymRef(child)) and not logic.isConstant(child); });
            } else if (logic.isNumEq(term.symb())) {
                if (not isPureArithmeticEquality(ptref, logic)) {
                    return rewriteInternal(ptref, [this](PTRef child) { return isArithmeticSymbol(logic, logic.getSymRef(child)) and not logic.isConstant(child); });
                }
            }
            return ptref;
        }

        Logic::SubstMap const & getPurificationMap() const { return freshVarMap; }
    };

    class Purifier : public Rewriter<PurifyConfig> {
        PurifyConfig config;

    public:
        Purifier(ArithLogic & logic)
            : Rewriter<PurifyConfig>(logic, config), config(logic) {}

        Logic::SubstMap const & getPurificationMap() const { return config.getPurificationMap(); }
    };
}

PTRef UFLATheory::purify(PTRef fla) {
    Purifier purifier(logic);
    PTRef rewritten = purifier.rewrite(fla);
    auto const & renameMap = purifier.getPurificationMap();
    vec<PTRef> equalities;
    equalities.capacity(renameMap.getSize() + 1);
    for (PTRef key : renameMap.getKeys()) {
        equalities.push(logic.mkEq(key, renameMap[key]));
    }
    equalities.push(rewritten);
    return logic.mkAnd(equalities);
}

template<typename Pred>
class RewriterConfig : public DefaultRewriterConfig {
    ArithLogic & logic;
    Pred pred;
public:
    RewriterConfig(ArithLogic & logic, Pred && pred) : logic(logic), pred(std::move(pred)) {}

    bool previsit(PTRef term) override { return logic.hasSortBool(term) and not logic.isIte(term); }

    PTRef rewrite(PTRef term) override {
        if (logic.isNumEq(term) and pred(term)) {
            Pterm const & p = logic.getPterm(term);
            PTRef a1 = p[0];
            PTRef a2 = p[1];
            PTRef i1 = logic.mkLeq(a1, a2);
            PTRef i2 = logic.mkGeq(a1, a2);
            return logic.mkAnd(i1, i2);
        }
        return term;
    }
};

PTRef UFLATheory::splitArithmeticEqualities(PTRef fla) {
    auto config = RewriterConfig(logic, [this](PTRef term) { return isPureArithmeticEquality(term, logic); } );
    auto rewriter = Rewriter(logic, config);
    return rewriter.rewrite(fla);
}

class CollectInterfaceVariablesConfig : public DefaultVisitorConfig {
    vec<PTRef> interfaceVars;
    ArithLogic & logic;

    enum class Type : char { Arith, Unint, Both };
    MapWithKeys<PTRef,Type, PTRefHash> occurrences;

    void updateOccurrenceUsingType(PTRef child, Type seenType) {
        Type t;
        if (not occurrences.peek(child, t)) {
            occurrences.insert(child, seenType);
            if (seenType == Type::Both) {
                interfaceVars.push(child);
            }
        } else {
            if (t != seenType and t != Type::Both) {
                occurrences[child] = Type::Both;
                interfaceVars.push(child);
            }
        }
    }
public:
    CollectInterfaceVariablesConfig(ArithLogic & logic) : DefaultVisitorConfig(), logic(logic) {}

    void visit(PTRef ptref) override {
        SymRef symbolRef = logic.getSymRef(ptref);
        if (isArithmeticSymbol(logic, symbolRef)) {
            for (PTRef child : logic.getPterm(ptref)) {
                if (logic.isVar(child) or logic.isNumConst(child)) {
                    updateOccurrenceUsingType(child, Type::Arith);
                }
            }
        } else if (isUninterpreted(logic, symbolRef) or logic.isEquality(symbolRef)) {
            for (PTRef child : logic.getPterm(ptref)) {
                if (logic.isNumVar(child) or logic.isNumConst(child)) {
                    updateOccurrenceUsingType(child, logic.isNumConst(child) ? Type::Both : Type::Unint);
                }
            }
        }
    }

    vec<PTRef> const & getInterfaceVars() const {
        return interfaceVars;
    }
};

PTRef UFLATheory::addInterfaceClauses(PTRef fla) {
    if (not logic.isAnd(fla)) { return fla; }
    CollectInterfaceVariablesConfig config(logic);
    TermVisitor(logic, config).visit(fla);
    vec<PTRef> const & interfaceVars = config.getInterfaceVars();
    // Add all interface clauses to the formula
    vec<PTRef> interfaceClauses;
    for (int i = 0; i < interfaceVars.size(); ++i) {
        for (int j = 0; j < i; ++j) {
            PTRef lhs = interfaceVars[i];
            PTRef rhs = interfaceVars[j];
            if (logic.isNumConst(lhs) and logic.isNumConst(rhs)) { continue; }
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
