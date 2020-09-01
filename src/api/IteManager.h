//
// Created by prova on 04.08.20.
//

#ifndef OPENSMT_ITEMANAGER_H
#define OPENSMT_ITEMANAGER_H

#include "Logic.h"

namespace ite {

    class CondValPair {
    public:
        PTRef cond;
        PTRef val;
        CondValPair(PTRef cond, PTRef val) : cond(cond), val(val) {}
    };

    class SwitchTable {
        SwitchTable* true_child;
        SwitchTable* false_child;
        const PTRef cond;
        const PTRef val;
    public:
        SwitchTable(PTRef cond, SwitchTable *true_table, SwitchTable *false_table) : true_child(true_table), false_child(false_table), cond(cond), val(PTRef_Undef) {}
        explicit SwitchTable(PTRef val) : true_child(nullptr), false_child(nullptr), cond(PTRef_Undef), val(val) {}
        PTRef getCond() const { return cond; }
        PTRef getVal() const { return val; }
        const SwitchTable *getTrueChild() const { return true_child; }
        const SwitchTable *getFalseChild() const { return false_child; }
    };

    class SwitchTables {
        Map<PTRef,ite::SwitchTable*,PTRefHash> tables;
        vec<ite::SwitchTable*> tablePointers;
        SwitchTable *newTable(PTRef tr);
        SwitchTable *newTable(PTRef tr, PTRef cond, ite::SwitchTable *true_table, ite::SwitchTable *false_table);
        static CondValPair getPathConstr(const SwitchTable *node, const std::map<const SwitchTable*,std::pair<lbool, const SwitchTable*>> &parents, Logic &logic);

    public:
        void clear() { for (auto table : tablePointers) { delete table; } tables.clear(); tablePointers.clear(); }
        ~SwitchTables() { clear(); }
        bool has(PTRef tr) { return tables.has(tr); }
        SwitchTable *getTableOrCreateLeafTable(PTRef tr) { return tables.has(tr) ? tables[tr] : newTable(tr); }
        void createAndStoreTable(PTRef tr, PTRef cond, ite::SwitchTable *true_table, ite::SwitchTable *false_table) {
            assert(not tables.has(tr)); newTable(tr, cond, true_table, false_table);
        }
        const SwitchTable *getTable(PTRef tr) { assert(tables.has(tr)); return tables[tr]; }

        SwitchTable* begin() { return tablePointers[0]; }
        const SwitchTable* begin() const { return tablePointers[0]; }
        SwitchTable* end() { return tablePointers.last(); }
        const SwitchTable* end() const { return tablePointers.last(); }
        vec<CondValPair> asConstrs(Logic &logic, PTRef ite) const;
    };
}

class IteManager {
    Logic &logic;
    Map<PTRef,bool,PTRefHash> ite_nodes;
    Map<PTRef,bool,PTRefHash> top_level_ites;
    Map<PTRef,PTRef,PTRefHash> ite_vars;
    bool isIteVar(PTRef tr) const { return top_level_ites.has(tr); }
    PTRef getTopLevelIte(PTRef tr) { assert (isIteVar(tr)); return ite_vars[tr]; }
    vec<PTRef> flat_top_level_switches;
    ite::SwitchTables switchTables;
    class timer {
        time_t start;
        const std::string name;
    public:
        timer(std::string&& name) : start(time(nullptr)), name(name) {}
        ~timer() { std::cout << name << ": " << time(nullptr) - start << std::endl; }
    };
public:
    explicit IteManager(Logic& l) : logic(l) {}

    void constructSwitchTables(PTRef root); // Construct the switch tables that define values for the Ite-terms
    void conjoinItes(PTRef root, PTRef& new_root);
    bool requiresSwitchTable(PTRef tr) {return top_level_ites.has(tr); } // Ite terms that are required to be computed through a switch table in the full formula
    const vec<PTRef> &getFlatTopLevelSwitches() { return flat_top_level_switches; }
    void clear() {
        ite_nodes.clear();
        top_level_ites.clear();
        ite_vars.clear();
        switchTables.clear();
    }
    void stackBasedDFS(PTRef root) const;
    void iterativeDFS(PTRef root) const;
    enum class type {
        white, gray, black
    };
    void DFS(PTRef root, vec<type> &flag) const;
};

#endif //OPENSMT_ITEMANAGER_H
