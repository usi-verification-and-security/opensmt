//
// Created by prova on 04.08.20.
//

#ifndef OPENSMT_ITETOSWITCH_H
#define OPENSMT_ITETOSWITCH_H

#include "Logic.h"


namespace ite {
    class timer {
        time_t start;
        const std::string name;
    public:
        explicit timer(std::string&& name) : start(time(nullptr)), name(name) {}
        ~timer() { std::cout << name << ": " << time(nullptr) - start << std::endl; }
    };

    struct NodeRef {
        uint32_t x;
        inline friend bool operator== (NodeRef a1, NodeRef a2)   { return a1.x == a2.x; }
        inline friend bool operator!= (NodeRef a1, NodeRef a2)   { return a1.x != a2.x; }
        inline friend bool operator< (NodeRef a1, NodeRef a2)    { return a1.x < a2.x;  }
    };

    static struct NodeRef NodeRef_Undef = {UINT32_MAX};


    class Node {
        friend class NodeAllocator;
        struct Tail {
            NodeRef true_child;
            NodeRef false_child;
            PTRef cond;
        };
        enum class NodeType { leaf = 0, inner = 1 };
        uint32_t id : 30;
        bool type : 1;
        PTRef term;
        Tail tail[0];
        void setCond(PTRef cond) { assert(!isLeaf()); tail[0].cond = cond; }
        void setTrueChild(NodeRef n) { assert(!isLeaf()); tail[0].true_child = n; }
        void setFalseChild(NodeRef n) { assert(!isLeaf()); tail[0].false_child = n; }
    public:
        Node(PTRef term, PTRef cond, NodeRef true_node, NodeRef false_node, uint32_t id);
        Node() = delete;
        bool isLeaf()           const { return NodeType(type) == NodeType::leaf; }
        PTRef getCond()         const { assert(!isLeaf()); return tail[0].cond; }
        PTRef getVal()          const { assert(isLeaf()); return term; }
        NodeRef getTrueChild()  const { return isLeaf() ? NodeRef_Undef : tail[0].true_child; }
        NodeRef getFalseChild() const { return isLeaf() ? NodeRef_Undef : tail[0].false_child; }
        int getId()             const { return id; }
        PTRef getTerm()         const { return term; }
    };

    class NodeAllocator : public RegionAllocator<uint32_t>
    {
        unsigned n_nodes;
        static unsigned iteNodeWord32Size(bool internalNode) {
            return sizeof(Node) + (internalNode ? sizeof(Node::Tail) : 0);
        }
    public:
        void clear() override { n_nodes = 0; RegionAllocator::clear(); }
        NodeAllocator() : n_nodes(0) {}
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

        Node       &operator[](NodeRef r)       { return (Node&)RegionAllocator<uint32_t>::operator[](r.x); }
        const Node &operator[](NodeRef r) const { return (Node&)RegionAllocator<uint32_t>::operator[](r.x); }
        Node*       lea       (NodeRef r)       { return (Node*)RegionAllocator<uint32_t>::lea(r.x); }
        const Node *lea       (NodeRef r) const { return (Node*)RegionAllocator<uint32_t>::lea(r.x); }
        NodeRef     ael       (const Node *t)   { auto r = RegionAllocator<uint32_t>::ael((uint32_t*)t); return {r}; }
        void        free      (NodeRef r)       {}
    };


    enum class type {
        white, gray, black
    };

    class CondValPair {
    public:
        PTRef cond;
        PTRef val;
        CondValPair(PTRef cond, PTRef val) : cond(cond), val(val) {}
        CondValPair() : cond(PTRef_Undef), val(PTRef_Undef) {}
    };



    class Dag {
        struct NodeRefLBool {
            NodeRef nr;
            lbool sign;
            NodeRefLBool() : nr(NodeRef_Undef), sign(l_Undef) {}
            NodeRefLBool(NodeRef nr, lbool sign): nr(nr), sign(sign) {};
            bool operator<(const NodeRefLBool& o) const {
                return (this->nr < o.nr) or (this->nr == o.nr and toInt(this->sign) < toInt(o.sign));
            }
        };
        NodeAllocator na;
        Map<PTRef,ite::NodeRef,PTRefHash> nodes;
        Map<PTRef,bool,PTRefHash> itePTRefs;
        vec<ite::NodeRef> nodeRefs;
        Map<PTRef,bool,PTRefHash> top_level_ites;
        std::set<NodeRef> leaves;
        NodeRef newNode(PTRef tr);
        NodeRef newNode(PTRef tr, PTRef cond, NodeRef true_node, NodeRef false_node);
        using ParentSet = std::set<NodeRefLBool>;

        NodeRef getNode(PTRef tr) { assert(nodes.has(tr)); return nodes[tr]; }
        const vec<NodeRef>& getNodes() const { return nodeRefs; }
        std::map<NodeRef,ParentSet> parents;
        void clear() { for (auto node : nodeRefs) { na.free(node); } nodes.clear(); nodeRefs.clear(); }
    public:
        Dag(Dag &&dag) = default;
        Dag() = default;
        ~Dag() { clear(); }
        NodeRef getNodeOrCreateLeafNode(PTRef tr) { return nodes.has(tr) ? nodes[tr] : newNode(tr); }
        void createAndStoreNode(PTRef tr, PTRef cond, NodeRef true_node, NodeRef false_node) {
            assert(not nodes.has(tr)); newNode(tr, cond, true_node, false_node);
        }

        void addItePTRef(PTRef tr) { itePTRefs.insert(tr, true); }
        bool isTopLevelIte(PTRef tr) const { return top_level_ites.has(tr) and top_level_ites[tr]; }
        void addTopLevelIte(PTRef tr) { top_level_ites.insert(tr, true); }
        vec<PTRef> getTopLevelItes() const { vec<PTRef> keys; top_level_ites.getKeys(keys); return keys; }
        Dag getReachableSubGraph(const Logic& logic, PTRef root);
        void annotateWithParentInfo(PTRef root);
        vec<ite::CondValPair> getCondValPairs(Logic& logic) const;
        // Debug
        void writeDagToStream(std::ostream&) const;
    };
}

class IteToSwitch {
protected:
    using type = ite::type;
    Logic &logic;
    Map<PTRef,PTRef,PTRefHash> ite_vars;
    vec<PTRef> flat_top_level_switches;
    ite::Dag iteDag;
    vec<PTRef> switches;
    PTRef makeSwitch(PTRef root);
    static ite::Dag constructIteDag(PTRef root, const Logic& l); // Construct the IteDag that define values for the Ite-terms
    void constructSwitches();

public:
    explicit IteToSwitch(Logic& l, PTRef root) : logic(l), iteDag(constructIteDag(root, l)) { constructSwitches(); }
    PTRef conjoin(PTRef root) { return logic.mkAnd(root, logic.mkAnd(switches)); };

    static void printDagToFile(const std::string &fname, const ite::Dag&);
    void printDagToFile(const std::string &fname) const { printDagToFile(fname, iteDag); };
};

#endif //OPENSMT_ITETOSWITCH_H
