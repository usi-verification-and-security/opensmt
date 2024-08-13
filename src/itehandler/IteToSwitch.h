//
// Created by prova on 04.08.20.
//

#ifndef OPENSMT_ITETOSWITCH_H
#define OPENSMT_ITETOSWITCH_H

#include <logics/Logic.h>

#include <iostream>
#include <map>
#include <set>

namespace opensmt::ite {
struct NodeRef {
    uint32_t x;
    inline friend bool operator==(NodeRef a1, NodeRef a2) { return a1.x == a2.x; }
    inline friend bool operator!=(NodeRef a1, NodeRef a2) { return a1.x != a2.x; }
    inline friend bool operator<(NodeRef a1, NodeRef a2) { return a1.x < a2.x; }
};

static NodeRef NodeRef_Undef = {UINT32_MAX};

class Node {
public:
    Node(PTRef term, PTRef cond, NodeRef true_node, NodeRef false_node, uint32_t id);

    bool isLeaf() const { return NodeType(type) == NodeType::leaf; }
    PTRef getCond() const {
        assert(!isLeaf());
        return tail[0].cond;
    }
    PTRef getVal() const {
        assert(isLeaf());
        return term;
    }
    NodeRef getTrueChild() const { return isLeaf() ? NodeRef_Undef : tail[0].true_child; }
    NodeRef getFalseChild() const { return isLeaf() ? NodeRef_Undef : tail[0].false_child; }
    int getId() const { return id; }
    PTRef getTerm() const { return term; }

private:
    friend class NodeAllocator;

    struct Tail {
        NodeRef true_child;
        NodeRef false_child;
        PTRef cond;
    };

    enum class NodeType { leaf = 0, inner = 1 };

    void setCond(PTRef cond) {
        assert(!isLeaf());
        tail[0].cond = cond;
    }
    void setTrueChild(NodeRef n) {
        assert(!isLeaf());
        tail[0].true_child = n;
    }
    void setFalseChild(NodeRef n) {
        assert(!isLeaf());
        tail[0].false_child = n;
    }

    uint32_t id : 30;
    bool type : 1;
    PTRef term;
    Tail tail[0];
};

class NodeAllocator : public RegionAllocator<uint32_t> {
public:
    NodeAllocator() : RegionAllocator<uint32_t>(1024), n_nodes(0) {}

    void clear() override {
        n_nodes = 0;
        RegionAllocator::clear();
    }

    unsigned getNumNodes() const { return n_nodes; }

    NodeRef alloc(PTRef term, PTRef cond, NodeRef trueChild, NodeRef falseChild) {
        assert((cond == PTRef_Undef) == (trueChild == NodeRef_Undef and falseChild == NodeRef_Undef));
        assert((trueChild == NodeRef_Undef) == (falseChild == NodeRef_Undef));
        uint32_t v = RegionAllocator<uint32_t>::alloc(static_cast<int>(iteNodeWord32Size(cond != PTRef_Undef)));
        NodeRef id = {v};
        new (lea(id)) Node(term, cond, trueChild, falseChild, n_nodes);
        n_nodes++;
        return id;
    }

    Node & operator[](NodeRef r) { return reinterpret_cast<Node &>(RegionAllocator<uint32_t>::operator[](r.x)); }
    Node const & operator[](NodeRef r) const {
        return reinterpret_cast<Node const &>(RegionAllocator<uint32_t>::operator[](r.x));
    }
    Node * lea(NodeRef r) { return reinterpret_cast<Node *>(RegionAllocator<uint32_t>::lea(r.x)); }
    Node const * lea(NodeRef r) const { return reinterpret_cast<Node const *>(RegionAllocator<uint32_t>::lea(r.x)); }
    NodeRef ael(Node const * t) {
        auto r = RegionAllocator<uint32_t>::ael((uint32_t *)t);
        return {r};
    }

    void free(NodeRef) {}

private:
    static unsigned iteNodeWord32Size(bool internalNode) {
        return (sizeof(Node) + (internalNode ? sizeof(Node::Tail) : 0)) / sizeof(uint32_t);
    }

    unsigned n_nodes;
};

enum class type : char { white, gray, black };

struct CondValPair {
    CondValPair() = default;
    CondValPair(PTRef cond, PTRef val) : cond(cond), val(val) {}

    PTRef cond{PTRef_Undef};
    PTRef val{PTRef_Undef};
};

class Dag {
public:
    Dag() = default;
    ~Dag() { clear(); }
    Dag(Dag && dag) = default;
    Dag & operator=(Dag && dag) = default;

    NodeRef getNodeOrCreateLeafNode(PTRef tr) { return nodes.has(tr) ? nodes[tr] : newNode(tr); }
    void createAndStoreNode(PTRef tr, PTRef cond, NodeRef true_node, NodeRef false_node) {
        assert(not nodes.has(tr));
        newNode(tr, cond, true_node, false_node);
    }

    void addItePTRef(PTRef tr) { itePTRefs.insert(tr, true); }
    bool isTopLevelIte(PTRef tr) const { return top_level_ites.has(tr) and top_level_ites[tr]; }
    void addTopLevelIte(PTRef tr) { top_level_ites.insert(tr, true); }
    vec<PTRef> const & getTopLevelItes() const { return top_level_ites.getKeys(); }
    Dag getReachableSubGraph(Logic const & logic, PTRef root);
    void annotateWithParentInfo(PTRef root);
    vec<ite::CondValPair> getCondValPairs(Logic & logic) const;

    // Debug
    void writeDagToStream(std::ostream &) const;

private:
    struct NodeRefLBool {
        NodeRefLBool() = default;
        NodeRefLBool(NodeRef nr, lbool sign) : nr(nr), sign(sign) {};

        bool operator<(NodeRefLBool const & o) const {
            return (this->nr < o.nr) or (this->nr == o.nr and toInt(this->sign) < toInt(o.sign));
        }

        NodeRef nr{NodeRef_Undef};
        lbool sign{l_Undef};
    };

    using ParentSet = std::set<NodeRefLBool>;

    void clear() {
        for (auto node : nodeRefs) {
            na.free(node);
        }
        nodes.clear();
        nodeRefs.clear();
    }

    NodeRef newNode(PTRef tr);
    NodeRef newNode(PTRef tr, PTRef cond, NodeRef true_node, NodeRef false_node);

    NodeRef getNode(PTRef tr) {
        assert(nodes.has(tr));
        return nodes[tr];
    }
    vec<NodeRef> const & getNodes() const { return nodeRefs; }

    NodeAllocator na;
    Map<PTRef, ite::NodeRef, PTRefHash> nodes;
    Map<PTRef, bool, PTRefHash> itePTRefs;
    vec<ite::NodeRef> nodeRefs;
    MapWithKeys<PTRef, bool, PTRefHash> top_level_ites;
    std::set<NodeRef> leaves;

    std::map<NodeRef, ParentSet> parents;
};
} // namespace opensmt::ite

namespace opensmt {
class IteToSwitch {
public:
    explicit IteToSwitch(Logic & l, PTRef root) : logic(l), iteDag(constructIteDag(root, l)) { constructSwitches(); }
    PTRef conjoin(PTRef root);

    static void printDagToFile(std::string const & fname, ite::Dag const &);
    void printDagToFile(std::string const & fname) const { printDagToFile(fname, iteDag); };

protected:
    using type = ite::type;

    PTRef makeSwitch(PTRef root);
    static ite::Dag constructIteDag(PTRef root,
                                    Logic const & l); // Construct the IteDag that define values for the Ite-terms
    void constructSwitches();

    Logic & logic;
    ite::Dag iteDag;
    vec<PTRef> switches;
};
} // namespace opensmt

#endif // OPENSMT_ITETOSWITCH_H
