//
// Created by Martin Blicha on 14.06.20.
//

#ifndef OPENSMT_MODELBUILDER_H
#define OPENSMT_MODELBUILDER_H

#include "Model.h"

#include <pterms/PTRef.h>

#include <memory>
#include <unordered_map>

namespace opensmt {
class Logic;

class ModelBuilder {
public:
    ModelBuilder(Logic & logic) : logic(logic), uniqueNum(0), formalArgDefaultPrefix("x") {}

    void addVarValue(PTRef var, PTRef value) {
        auto res = assignment.insert(std::make_pair(var, value));
        assert(res.second);
        (void)res;
    }

    inline bool hasVarVal(PTRef term) const {
        assert(logic.isVar(term));
        return assignment.find(term) != assignment.end();
    }

    inline PTRef getVarVal(PTRef term) const {
        assert(hasVarVal(term));
        return assignment.at(term);
    }

    template<typename TIt>
    void addVarValues(TIt begin, TIt end) {
        assignment.insert(begin, end);
    }

    bool hasTheoryFunction(SymRef sr) const { return definitions.find(sr) != definitions.end(); }
    bool hasTheoryFunction(PTRef tr) const { return hasTheoryFunction(logic.getSymRef(tr)); }

    void addToTheoryFunction(SymRef sr, vec<PTRef> const & vals, PTRef val);

    template<typename TIt>
    void addFunctionDefinitions(TIt begin, TIt end) {
        definitions.insert(begin, end);
    }

    std::unique_ptr<Model> build();

protected:
    class ValuationNodeFactory;
    class ValuationNode {
    public:
        bool operator==(ValuationNode const * o) const { return this->id == o->id; }
        ValuationNode * operator[](int i) { return children[i]; }
        ValuationNode const * operator[](int i) const { return children[i]; }
        std::size_t nChildren() const { return children.size(); }
        bool hasChildren() const { return not children.empty(); }
        int getId() const { return id; }
        PTRef getValue() const { return value; }
        PTRef getVar() const { return var; }
        std::vector<ModelBuilder::ValuationNode *>::iterator begin() { return children.begin(); }
        std::vector<ModelBuilder::ValuationNode *>::iterator end() { return children.end(); }
        ValuationNode * addChild(ValuationNode * n) {
            children.emplace_back(n);
            return n;
        }

    private:
        friend class ModelBuilder::ValuationNodeFactory;

        ValuationNode(int id) : id(id), value{PTRef_Undef}, var{PTRef_Undef} {}
        ValuationNode(int id, PTRef var, PTRef val) : id(id), value{val}, var{var} { assert(var != PTRef_Undef); }

        int id;
        std::vector<ValuationNode *> children;
        PTRef value;
        PTRef var;
    };

    struct ValuationNodeHash {
        std::size_t operator()(ValuationNode const * n) const { return std::hash<int>()(n->getId()); }
    };

    class ValuationNodeFactory {
    public:
        ValuationNodeFactory() : numValuationNodes(0) {}
        ~ValuationNodeFactory() {
            for (auto n : nodes) {
                delete n;
            }
        }
        ValuationNode * getValuationNode() {
            auto vn = new ValuationNode(numValuationNodes++);
            nodes.push(vn);
            return vn;
        }
        ValuationNode * getValuationNode(PTRef var, PTRef val) {
            auto vn = new ValuationNode(numValuationNodes++, var, val);
            nodes.push(vn);
            return vn;
        }
        int numNodes() const { return nodes.size(); }

    private:
        int numValuationNodes;
        vec<ValuationNode *> nodes;
    };

    ValuationNode * addToValuationTree(vec<opensmt::pair<PTRef, PTRef>> const & valuation, PTRef value,
                                       ValuationNode * root);
    PTRef valuationTreeToFunctionBody(ValuationNode const *, SRef sr);

    ValuationNodeFactory valuationNodeFactory;

    std::unordered_map<PTRef, PTRef, PTRefHash> assignment;
    std::unordered_map<SymRef, opensmt::pair<FunctionSignature, ValuationNode *>, SymRefHash> definitions;

    Logic & logic;
    int uniqueNum;
    std::string const formalArgDefaultPrefix;
};

} // namespace opensmt

#endif // OPENSMT_MODELBUILDER_H
