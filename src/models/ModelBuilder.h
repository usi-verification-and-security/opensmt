//
// Created by Martin Blicha on 14.06.20.
//

#ifndef OPENSMT_MODELBUILDER_H
#define OPENSMT_MODELBUILDER_H

#include "PTRef.h"
#include "Model.h"

#include <unordered_map>
#include <memory>

class Logic;

class ModelBuilder {
protected:
    class ValuationNodeFactory;
    class ValuationNode {
        friend class ModelBuilder::ValuationNodeFactory;
        int id;
        std::vector<ValuationNode*> children;
        PTRef value;
        PTRef var;
        ValuationNode(int id) : id(id), value{PTRef_Undef}, var{PTRef_Undef} {}
        ValuationNode(int id, PTRef var, PTRef val) : id(id), value{val}, var{var} { assert(var != PTRef_Undef); }
    public:
        bool operator== (const ValuationNode* o) const { return this->id == o->id; }
        ValuationNode* operator[] (int i) { return children[i]; }
        const ValuationNode* operator[] (int i) const { return children[i]; }
        std::size_t nChildren() const { return children.size(); }
        bool hasChildren() const { return not children.empty(); }
        int getId() const { return id; }
        PTRef getValue() const { return value; }
        PTRef getVar() const { return var; }
        std::vector<ModelBuilder::ValuationNode*>::iterator begin() { return children.begin(); }
        std::vector<ModelBuilder::ValuationNode*>::iterator end() { return children.end(); }
        ValuationNode* addChild(ValuationNode* n) { children.emplace_back(n); return n; }
    };
    struct ValuationNodeHash {
        std::size_t operator() (const ValuationNode* n) const { return std::hash<int>()(n->getId()); }
    };
    class ValuationNodeFactory {
        int numValuationNodes;
        vec<ValuationNode*> nodes;
    public:
        ValuationNodeFactory() : numValuationNodes(0) {}
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
        ~ValuationNodeFactory() { for (auto n : nodes) { delete n; } }
    };
    ValuationNodeFactory valuationNodeFactory;
    ValuationNode * addToValuationTree(const vec<opensmt::pair<PTRef,PTRef>> & valuation, PTRef value, ValuationNode * root);
    PTRef valuationTreeToFunctionBody(const ValuationNode *, SRef sr);

    std::unordered_map<PTRef, PTRef, PTRefHash> assignment;
    std::unordered_map<SymRef, opensmt::pair<FunctionSignature, ValuationNode*>, SymRefHash> definitions;

    Logic& logic;
    int uniqueNum;
    const std::string formalArgDefaultPrefix;

public:

    ModelBuilder(Logic & logic) : logic(logic), uniqueNum(0), formalArgDefaultPrefix("x") {}

    void addVarValue(PTRef var, PTRef value) {
        auto res = assignment.insert(std::make_pair(var, value));
        assert(res.second); (void)res;
    }

    template<typename TIt>
    void addVarValues(TIt begin, TIt end) {
        assignment.insert(begin, end);
    }

//    void addFunctionDefinition(SymRef sym, Logic::TFun templateFunction) {
//        auto res = definitions.insert(std::make_pair(sym, templateFunction));
//        assert(res.second); (void)res;
//    }
    bool hasTheoryFunction(SymRef sr) const { return definitions.find(sr) != definitions.end();}
    bool hasTheoryFunction(PTRef tr) const { return hasTheoryFunction(logic.getSymRef(tr)); }

    void addToTheoryFunction(SymRef sr, vec<PTRef> vals, PTRef val);

    template<typename TIt>
    void addFunctionDefinitions(TIt begin, TIt end) {
        definitions.insert(begin, end);
    }

    std::unique_ptr<Model> build();
};


#endif //OPENSMT_MODELBUILDER_H
