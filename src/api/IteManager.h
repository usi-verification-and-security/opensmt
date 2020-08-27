//
// Created by prova on 04.08.20.
//

#ifndef OPENSMT_ITEMANAGER_H
#define OPENSMT_ITEMANAGER_H

#include "Logic.h"

namespace ite {
    struct SwitchRow {
        PTRef value;
        vec<PtAsgn> constrs;
        SwitchRow prepend(PtAsgn cond) const;
        explicit SwitchRow(PTRef tr) : value(tr) {}
        SwitchRow(SwitchRow&& o) noexcept : value(o.value), constrs(std::move(o.constrs)) {}
        SwitchRow() : value(PTRef_Undef) {}
        SwitchRow& operator= (SwitchRow&& o) noexcept { value = o.value; constrs = std::move(o.constrs); return *this; }
    };

    class SwitchTable {
        vec<SwitchRow> rows;
    public:
        SwitchTable(PTRef cond, const SwitchTable &true_table, const SwitchTable &false_table);
        explicit SwitchTable(PTRef tr) { rows.push_m(SwitchRow(tr)); }
        PTRef asConstrs(Logic &logic, PTRef target) const;
    };

    class SwitchTables {
        Map<PTRef,ite::SwitchTable*,PTRefHash> tables;
        vec<ite::SwitchTable*> tablePointers;
        SwitchTable *newTable(PTRef tr) { tablePointers.push(new ite::SwitchTable(tr)); tables.insert(tr, tablePointers.last()); return tablePointers.last(); }
        SwitchTable *newTable(PTRef tr, PTRef cond, ite::SwitchTable *true_table, ite::SwitchTable *false_table) {
            tablePointers.push(new ite::SwitchTable(cond, *true_table, *false_table));
            tables.insert(tr, tablePointers.last()); return tablePointers.last();
        }
    public:
        void clear() { for (auto table : tablePointers) { delete table; } tables.clear(); tablePointers.clear(); }
        ~SwitchTables() { clear(); }
        bool has(PTRef tr) { return tables.has(tr); }
        SwitchTable *getOrCreateSimpleTable(PTRef tr) { return tables.has(tr) ? tables[tr] : newTable(tr); }
        void createAndStoreTable(PTRef tr, PTRef cond, ite::SwitchTable *true_table, ite::SwitchTable *false_table) {
            assert(not tables.has(tr)); newTable(tr, cond, true_table, false_table);
        }
        const SwitchTable *getTable(PTRef tr) { assert(tables.has(tr)); return tables[tr]; }
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
};

#endif //OPENSMT_ITEMANAGER_H
