//
// Created by prova on 28.03.22.
//

#ifndef OPENSMT_TERMPRINTER_H
#define OPENSMT_TERMPRINTER_H

#include "TreeOps.h"
#include "PTRef.h"

class ReferenceCounterConfig : public DefaultVisitorConfig {
    Logic const &logic;
    Map<PTRef, int, PTRefHash> previsitCount;
    std::unordered_map<PTRef, int, PTRefHash> referenceCounts;
public:
    ReferenceCounterConfig(Logic const &logic) : logic(logic) {}
    bool previsit(PTRef tr);
    std::unordered_map<PTRef, int, PTRefHash> & getReferences() { return referenceCounts; };
};

class TermPrinterConfig : public DefaultVisitorConfig {
    Logic const & logic;
    std::unordered_map<PTRef, int, PTRefHash> & refCounts;
    std::unordered_map<PTRef,std::string,PTRefHash> termStrings;
public:
    TermPrinterConfig(Logic const & logic, std::unordered_map<PTRef, int, PTRefHash> & refCounts) : logic(logic), refCounts(refCounts) {}
    void visit(PTRef tr);
    std::string print(PTRef tr) { return termStrings.at(tr); }
};

class TermPrinter {
    Logic const & logic;
    std::unordered_map<PTRef, std::string, PTRefHash> termStrings;
public:
    TermPrinter(Logic const & logic) : logic(logic) {}
    std::string print(PTRef tr) {
        ReferenceCounterConfig counter(logic);
        TermVisitor(logic, counter).visit(tr);
        TermPrinterConfig printer(logic, counter.getReferences());
        TermVisitor(logic, printer).visit(tr);
        return printer.print(tr);
    }
};

class DagPrinterConfig : public DefaultVisitorConfig {
    Logic const & logic;
    std::unordered_map<PTRef, int, PTRefHash> & refCounts;

    std::unordered_map<PTRef,std::string,PTRefHash> termStrings;
    std::unordered_map<PTRef,vec<PTRef>,PTRefHash> const & definitions;
    std::unordered_set<PTRef,PTRefHash> const & letDefinedTerms;
    bool isLetDefined(PTRef tr) const { return letDefinedTerms.find(tr) != letDefinedTerms.end(); }
public:
    DagPrinterConfig(Logic const & logic,
                     std::unordered_map<PTRef, int, PTRefHash> & refCounts,
                     std::unordered_map<PTRef,vec<PTRef>,PTRefHash> const & definitions,
                     std::unordered_set<PTRef,PTRefHash> const & letDefinedTerms)
    : logic(logic)
    , refCounts(refCounts)
    , definitions(definitions)
    , letDefinedTerms(letDefinedTerms)
    {}
    void visit(PTRef tr) override;
    std::string print(PTRef tr) { assert(termStrings.size() == 1); return termStrings[tr]; }
};

class SubGraphVisitorConfig : public DefaultVisitorConfig {
    Logic const & logic;
    PTRef root;
    class NodeFactory {
    public:
        struct Node {
            std::vector<Node *> parents;
            PTRef tr;
            void addParent(Node *c) {
                parents.push_back(c);
            }
        };
        std::vector<Node *> nodes;
        std::unordered_map<PTRef,NodeFactory::Node *,PTRefHash> ptrefToNode;
    public:
        ~NodeFactory() {
            for (auto n : nodes) {
                delete n;
            }
        }
        Node * addNode(PTRef tr) {
            auto n = new Node{{}, tr};
            nodes.push_back(n);
            ptrefToNode.insert({tr, n});
            return n;
        }
        Node * findNode(PTRef tr) const { auto el = ptrefToNode.find(tr); return (el == ptrefToNode.end()) ? nullptr : el->second; }
    };

    NodeFactory nodeFactory;

    struct DFSElement {
        NodeFactory::Node * node;
        unsigned processedEdges;
        DFSElement(NodeFactory::Node * node, int processedEdges) : node(node), processedEdges(processedEdges) {}
    };

public:
    SubGraphVisitorConfig(Logic const & logic, PTRef root) : logic(logic), root(root) {}

    bool isAnAncestor(PTRef t, PTRef ancestor);

    void visit(PTRef tr) override {
        assert(nodeFactory.findNode(tr) == nullptr);
        auto node = nodeFactory.addNode(tr);
        for (auto childRef: logic.getPterm(tr)) {
            auto child = nodeFactory.findNode(childRef);
            assert(child);
            child->addParent(node);
        }
    }

    std::vector<PTRef> removeReversePath(PTRef n, PTRef tr);
    PTRef findFirstMissingEdge(std::vector<PTRef> const & path) const;
};

class DagPrinter {
    Logic const & logic;
public:
    DagPrinter(Logic const & logic) : logic(logic) {}
    std::string print(PTRef tr);
};

#endif //OPENSMT_TERMPRINTER_H
