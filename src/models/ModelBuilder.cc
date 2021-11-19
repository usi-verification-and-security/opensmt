//
// Created by Martin Blicha on 14.06.20.
//

#include "ModelBuilder.h"

#include <sstream>
#include <unordered_set>

std::unique_ptr<Model> ModelBuilder::build() {
    std::unordered_map<SymRef,TemplateFunction,SymRefHash> builtDefinitions;
    for (auto & symbolSigVal : definitions) {
        const ValuationNode * valuationNode = symbolSigVal.second.second;
        SRef sr = logic.getSortRef(symbolSigVal.first);
        PTRef body = valuationTreeToFunctionBody(valuationNode, sr);
        TemplateFunction templateFun(std::move(symbolSigVal.second.first), body);
        builtDefinitions[symbolSigVal.first] = std::move(templateFun);
    }
    return std::make_unique<Model>(logic, assignment, builtDefinitions);
}

void ModelBuilder::addToTheoryFunction(SymRef sr, const vec<PTRef> & vals, PTRef val)
{
    if (logic.getSortRef(sr) != logic.getSortRef(val)) {
        throw OsmtApiException("Incompatible sort for symbol valuation");
    }
    const Symbol & sym = logic.getSym(sr);
    if (sym.nargs() != vals.size_()) {
        throw OsmtApiException("Incorrect valuation for symbol: argument and valuation size do not match");
    }
    for (int i = 0; i < vals.size(); i++) {
        if (sym[i] != logic.getSortRef(vals[i])) {
            throw OsmtApiException("Incorrect valuation for symbol: sort mismatch");
        }
    }

    if (not hasTheoryFunction(sr)) {
        vec<PTRef> formalArgs; formalArgs.capacity(vals.size());
        // Ensure that no formal arg name collides with the function name
        std::string formalArgPrefix(Model::getFormalArgBaseNameForSymbol(logic, sr, formalArgDefaultPrefix));

        for (PTRef v : vals) {
            std::stringstream ss;
            ss << formalArgPrefix << uniqueNum++;
            formalArgs.push(logic.mkVar(logic.getSortRef(v), ss.str().c_str()));
        }
        FunctionSignature templateSig(logic.protectName(logic.getSymName(sr)), std::move(formalArgs), logic.getSortRef(sr));
        definitions.insert({sr,opensmt::pair<FunctionSignature,ValuationNode*>{std::move(templateSig), nullptr}});
    }
    auto & signatureAndValuation = definitions.at(sr);
    const vec<PTRef> & formalArgs = signatureAndValuation.first.getArgs();
    vec<opensmt::pair<PTRef,PTRef>> valuation; valuation.capacity(vals.size());
    for (int i = 0; i < vals.size(); i++) {
        valuation.push({formalArgs[i], vals[i]});
    }
    assert(logic.getSortRef(val) == logic.getSortRef(sr));
    signatureAndValuation.second = addToValuationTree(valuation, val, signatureAndValuation.second);
}

ModelBuilder::ValuationNode * ModelBuilder::addToValuationTree(const vec<opensmt::pair<PTRef,PTRef>> & valuation, PTRef value, ValuationNode * root) {
    assert(valuation.size() >= 1);

    if (root == nullptr) {
        root = valuationNodeFactory.getValuationNode(valuation[0].first, PTRef_Undef);
    }

    ValuationNode * current = root;

    for (int i = 0; i < valuation.size(); i++) {
        PTRef val = valuation[i].second; // The value of my parent's var

        assert(current != nullptr);

        bool foundChild = false;
        for (auto child: *current) {
            if (child->getValue() == val) {
                current = child;
                foundChild = true;
                break;
            }
        }
        if (not foundChild) {
            // No child found with this value.  Need to create a new child.  If this will be a leaf
            // (i.e., it is the last value in a valuation) the var will by convention be set to the
            // value of this valuation
            current = current->addChild(valuationNodeFactory.getValuationNode(i == valuation.size()-1 ? value : valuation[i+1].first, val));
        }
    }
    return root;
}

// Copied from TermVisitor.  Maybe it'd be possible to template TermVisitor to handle also ValuationNodes
PTRef ModelBuilder::valuationTreeToFunctionBody(const ValuationNode *root, SRef returnSort) {
    struct QPair {
        const ValuationNode * node;
        std::size_t nextChild;
        QPair(const ValuationNode* n) : node(n), nextChild(0) {}
    };

    std::unordered_map<const ValuationNode*,PTRef,ValuationNodeHash> nodeToFormula;

    vec<char> done(valuationNodeFactory.numNodes(), 0);

    vec<QPair> queue;
    queue.push(QPair{root});
    while (queue.size() != 0) {
        auto & el = queue.last();
        auto * node = el.node;
        assert(not done[node->getId()]);
        if (el.nextChild < node->nChildren()) {
            const ValuationNode *child = (*node)[el.nextChild];
            el.nextChild ++;
            if (not done[child->getId()]) {
                queue.push({QPair{child}});
            }
            continue;
        }
        // All children of the node are processed
        assert(done[node->getId()] == 0);
        if (not node->hasChildren()) {
            // Base case: the node is a leaf value node.
            nodeToFormula[node] = node->getVar();
            assert(logic.getSortRef(node->getVar()) == returnSort);
        } else {
            PTRef nodeFormula = logic.getDefaultValuePTRef(returnSort);
            for (int i = node->nChildren()-1; i >= 0; i--) {
                nodeFormula = logic.mkIte(logic.mkEq(node->getVar(), (*node)[i]->getValue()), nodeToFormula.at((*node)[i]), nodeFormula);
            }
            nodeToFormula[node] = nodeFormula;
        }
        done[node->getId()] = 1;
        queue.pop();
    }
    return nodeToFormula[root];
}