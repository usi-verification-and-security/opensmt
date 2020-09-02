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
        timer(std::string&& name) : start(time(nullptr)), name(name) {}
        ~timer() { std::cout << name << ": " << time(nullptr) - start << std::endl; }
    };

    class CondValPair {
    public:
        PTRef cond;
        PTRef val;
        CondValPair(PTRef cond, PTRef val) : cond(cond), val(val) {}
    };

    class IteDagNode {
        static int id_count;
        int id;
        IteDagNode* true_child;
        IteDagNode* false_child;
        const PTRef cond;
        const PTRef val;
        const PTRef term;
    public:
        IteDagNode(PTRef term, PTRef cond, IteDagNode *true_table, IteDagNode *false_table) : id(id_count++), true_child(true_table), false_child(false_table), cond(cond), val(PTRef_Undef), term(term) {}
        explicit IteDagNode(PTRef term, PTRef val) : id(id_count++), true_child(nullptr), false_child(nullptr), cond(PTRef_Undef), val(val), term(term) {}
        PTRef getCond() const { return cond; }
        PTRef getVal() const { return val; }
        const IteDagNode *getTrueChild() const { return true_child; }
        const IteDagNode *getFalseChild() const { return false_child; }
        int getId() const { return id; }
        PTRef getTerm() const { return term; }
        static const int getIdCount() { return id_count; }
    };

    class IteParentRecord {
        lbool sign;
        const IteDagNode *parent;
        PTRef pathFormula;
    public:
        IteParentRecord(IteParentRecord&&) = default;
        IteParentRecord& operator=(IteParentRecord&&) = default;
        IteParentRecord() : sign(l_Undef), parent(nullptr), pathFormula(PTRef_Undef) {}
        IteParentRecord(lbool sign, const IteDagNode* parent) : sign(sign), parent(parent), pathFormula(PTRef_Undef) {}
        void setPathFormula(PTRef pf) { pathFormula = pf; }
        PTRef getPathFormula() const { return pathFormula; }
        const IteDagNode* getNode() const { return parent; }
        lbool getSign() const { return sign; }
    };

    class IteDag {
        Map<PTRef,ite::IteDagNode*,PTRefHash> nodes;
        Map<PTRef,bool,PTRefHash> itePTRefs;
        vec<ite::IteDagNode*> nodePointers;
        Map<PTRef,bool,PTRefHash> top_level_ites;

        IteDagNode *newNode(PTRef tr);
        IteDagNode *newNode(PTRef tr, PTRef cond, ite::IteDagNode *true_table, ite::IteDagNode *false_table);
        static CondValPair getPathConstr(const IteDagNode *node, std::map<const IteDagNode*,IteParentRecord> &parents, Logic &logic);

    public:
        IteDag(IteDag &&dag) = default;
        IteDag() = default;
        void clear() { for (auto node : nodePointers) { delete node; } nodes.clear(); nodePointers.clear(); }
        ~IteDag() { clear(); }
        bool has(PTRef tr) { return nodes.has(tr); }
        IteDagNode *getNodeOrCreateLeafNode(PTRef term, PTRef tr) { return nodes.has(tr) ? nodes[tr] : newNode(tr); }
        void createAndStoreNode(PTRef tr, PTRef cond, ite::IteDagNode *true_node, ite::IteDagNode *false_node) {
            assert(not nodes.has(tr)); newNode(tr, cond, true_node, false_node);
        }
        const IteDagNode *getNode(PTRef tr) { assert(nodes.has(tr)); return nodes[tr]; }

        const vec<IteDagNode*>& getIteDagNodes() const { return nodePointers; }

        vec<CondValPair> asConstrs(Logic &logic, PTRef ite) const;
        void addItePTRef(PTRef tr) { itePTRefs.insert(tr, true); }
        bool isTopLevelIte(PTRef tr) const { return top_level_ites.has(tr) and top_level_ites[tr]; }
        void addTopLevelIte(PTRef tr) { top_level_ites.insert(tr, true); }
        vec<PTRef> getTopLevelItes() const { vec<PTRef> keys; top_level_ites.getKeys(keys); return keys; }
        IteDag getReachableSubGraph(const Logic& logic, PTRef root);
        std::stringstream getDagAsStream() const;
    };
}

class IteManager {
    Logic &logic;
    Map<PTRef,bool,PTRefHash> ite_nodes;
    Map<PTRef,PTRef,PTRefHash> ite_vars;
    bool isIteVar(PTRef tr) const { return iteDag.isTopLevelIte(tr); }
    PTRef getTopLevelIte(PTRef tr) { assert (isIteVar(tr)); return ite_vars[tr]; }
    vec<PTRef> flat_top_level_switches;
    ite::IteDag iteDag;

public:
    explicit IteManager(Logic& l, PTRef root) : logic(l), iteDag(constructIteDag(root, l)) {}

    static ite::IteDag constructIteDag(PTRef root, const Logic& l); // Construct the IteDag that define values for the Ite-terms
    void traverseTopLevelItes();
    void conjoinItes(PTRef root, PTRef& new_root);
    bool requiresIteDag(PTRef tr) {return iteDag.isTopLevelIte(tr); } // Ite terms that are required to be computed through a switch table in the full formula
    const vec<PTRef> &getFlatTopLevelSwitches() const { return flat_top_level_switches; }

    void stackBasedDFS(PTRef root) const;
    void iterativeDFS(PTRef root) const;
    enum class type {
        white, gray, black
    };
    void DFS(PTRef root, vec<type> &flag) const;

    static void printDagToFile(const std::string &fname, const ite::IteDag&);
    void printDagToFile(const std::string &fname) const { printDagToFile(fname, iteDag); };
};

#endif //OPENSMT_ITEMANAGER_H
