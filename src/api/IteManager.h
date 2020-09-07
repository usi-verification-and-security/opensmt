//
// Created by prova on 04.08.20.
//

#ifndef OPENSMT_ITEMANAGER_H
#define OPENSMT_ITEMANAGER_H

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
    struct NodeRef_lt {
        bool operator() (const NodeRef &n1, const NodeRef &n2) const { return n1 < n2; }
    };
    static struct NodeRef NodeRef_Undef = {INT32_MAX};

    struct NodeRefHash {
        uint32_t operator () (const PTRef& s) const {
            return (uint32_t)s.x; }
    };
    struct NodeRefLBoolHash {
        uint32_t operator () (const std::pair<NodeRef,lbool> &s) const {
            std::hash<uint32_t> hasher;
            return hasher(s.first.x) ^ hasher(toInt(s.second));
        }
    };
    struct NodeRefLBool_lt {
        uint32_t operator () (const std::pair<NodeRef,lbool> &s1, const std::pair<NodeRef,lbool> &s2) const {
            return (s1.first < s2.first) or (s1.first == s2.first and toInt(s1.second) < toInt(s2.second));
        }
    };
    class Node {
        friend class NodeAllocator;
        struct Tail {
            NodeRef true_child;
            NodeRef false_child;
            PTRef cond;
        };
        enum class NodeType { leaf = 0, inner = 1 };
        uint32_t id : 31;
        NodeType type : 1;
        PTRef term;
        Tail tail[0];
        void setCond(PTRef cond) { assert(!isLeaf()); tail[0].cond = cond; }
        void setTrueChild(NodeRef n) { assert(!isLeaf()); tail[0].true_child = n; }
        void setFalseChild(NodeRef n) { assert(!isLeaf()); tail[0].false_child = n; }
    public:
        Node(PTRef term, PTRef cond, NodeRef true_node, NodeRef false_node, uint32_t id);
        Node() = delete;
        bool isLeaf()           const { return type == NodeType::leaf; }
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
        NodeAllocator na;
        Map<PTRef,ite::NodeRef,PTRefHash> nodes;
        Map<PTRef,bool,PTRefHash> itePTRefs;
        vec<ite::NodeRef> nodeRefs;
        Map<PTRef,bool,PTRefHash> top_level_ites;
        std::set<NodeRef, ite::NodeRef_lt> leaves;

        NodeRef newNode(PTRef tr);
        NodeRef newNode(PTRef tr, PTRef cond, NodeRef true_node, NodeRef false_node);
        using ParentSet = std::set<std::pair<NodeRef,lbool>,NodeRefLBool_lt>;

        std::map<NodeRef,ParentSet,NodeRef_lt> parents;
    public:
        Dag(Dag &&dag) = default;
        Dag() = default;
        void clear() { for (auto node : nodeRefs) { na.free(node); } nodes.clear(); nodeRefs.clear(); }
        ~Dag() { clear(); }
        bool has(PTRef tr) { return nodes.has(tr); }
        NodeRef getNodeOrCreateLeafNode(PTRef tr) { return nodes.has(tr) ? nodes[tr] : newNode(tr); }
        void createAndStoreNode(PTRef tr, PTRef cond, NodeRef true_node, NodeRef false_node) {
            assert(not nodes.has(tr)); newNode(tr, cond, true_node, false_node);
        }
        NodeRef getNode(PTRef tr) { assert(nodes.has(tr)); return nodes[tr]; }

        const vec<NodeRef>& getNodes() const { return nodeRefs; }

        void addItePTRef(PTRef tr) { itePTRefs.insert(tr, true); }
        bool isTopLevelIte(PTRef tr) const { return top_level_ites.has(tr) and top_level_ites[tr]; }
        void addTopLevelIte(PTRef tr) { top_level_ites.insert(tr, true); }
        vec<PTRef> getTopLevelItes() const { vec<PTRef> keys; top_level_ites.getKeys(keys); return keys; }
        Dag getReachableSubGraph(const Logic& logic, PTRef root);
        void annotateWithParentInfo(NodeRef root);
        vec<ite::CondValPair> getCondValPairs(Logic& logic) const;
        // Debug
        std::stringstream getDagAsStream() const;
    };
}

class IteManager {
    using type = ite::type;
    Logic &logic;
    Map<PTRef,bool,PTRefHash> ite_nodes;
    Map<PTRef,PTRef,PTRefHash> ite_vars;
    bool isIteVar(PTRef tr) const { return iteDag.isTopLevelIte(tr); }
    PTRef getTopLevelIte(PTRef tr) { assert (isIteVar(tr)); return ite_vars[tr]; }
    vec<PTRef> flat_top_level_switches;
    ite::Dag iteDag;
    vec<PTRef> switches;

public:
    explicit IteManager(Logic& l, PTRef root) : logic(l), iteDag(constructIteDag(root, l)) {}

    static ite::Dag constructIteDag(PTRef root, const Logic& l); // Construct the IteDag that define values for the Ite-terms
    void conjoinSwitches(PTRef root, PTRef& new_root) { new_root = logic.mkAnd(root, logic.mkAnd(switches)); };
    const vec<PTRef> &getFlatTopLevelSwitches() const { return flat_top_level_switches; }

    PTRef makeSwitch(PTRef root);

    // Debug
    void stackBasedDFS(PTRef root) const;
    void iterativeDFS(PTRef root) const;

    void DFS(PTRef root, vec<type> &flag) const;

    static void printDagToFile(const std::string &fname, const ite::Dag&);
    void printDagToFile(const std::string &fname) const { printDagToFile(fname, iteDag); };
    void traverseTopLevelItes();
};

#endif //OPENSMT_ITEMANAGER_H
