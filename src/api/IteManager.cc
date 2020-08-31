//
// Created by prova on 04.08.20.
//

#include "IteManager.h"
#include "Logic.h"

ite::SwitchTable* ite::SwitchTables::newTable(PTRef val) {
    assert(not tables.has(val));
    tablePointers.push(new ite::SwitchTable(val));
    tables.insert(val, tablePointers.last());
    return tablePointers.last();
}

ite::SwitchTable* ite::SwitchTables::newTable(PTRef tr, PTRef cond, ite::SwitchTable *true_table, ite::SwitchTable *false_table)
{
    assert(not tables.has(tr));
    tablePointers.push(new ite::SwitchTable(cond, true_table, false_table));
    tables.insert(tr, tablePointers.last());
    return tablePointers.last();
}

ite::CondValPair ite::SwitchTables::getPathConstr(const SwitchTable *leaf, const std::map<const SwitchTable*,std::pair<lbool,const SwitchTable*>> &parents, Logic &logic) {
    assert(leaf->getCond() == PTRef_Undef);
    assert(leaf->getVal() != PTRef_Undef);
    assert(not logic.isIte(leaf->getVal()));

    vec<PTRef> path;
    const SwitchTable *node = leaf;
    while (parents.find(node) != parents.end()) {
        const auto &parent = parents.at(node);
        node = parent.second;
        assert(node->getCond() != PTRef_Undef);
        assert(node->getVal() == PTRef_Undef);
        lbool sign = parent.first;
        PTRef tr = node->getCond();
        path.push(sign == l_True ? tr : logic.mkNot(tr));
    }
    return {logic.mkAnd(path), leaf->getVal()};
}

vec<ite::CondValPair> ite::SwitchTables::asConstrs(Logic &logic, PTRef target) const {
    assert(tables.has(target));
    assert(logic.isIte(target));

    std::map<const SwitchTable*,std::pair<lbool, const SwitchTable*>> parents;
    vec<const SwitchTable*> queue;

    queue.push(tables[target]);

    vec<CondValPair> constrs;

    while (queue.size() != 0) {
        const SwitchTable *table = queue.last();
        queue.pop();

        bool isLeaf = true;
        for (lbool child_cond : {l_True, l_False}) {
            const SwitchTable *child = (child_cond == l_True ? table->getTrueChild() : table->getFalseChild());
            if (child != nullptr) {
                queue.push(child);
                parents[table] = {child_cond, child};
                isLeaf = false;
            }
        }
        if (isLeaf) {
            auto row = getPathConstr(table, parents, logic);
            constrs.push(row);
        }
    }
    return constrs;
}

void IteManager::stackBasedDFS(PTRef root) const {


    vec<PTRef> queue;

    vec<type> flag;
    flag.growTo(logic.getNumberOfTerms());

    DFS(root, flag);
}

void IteManager::DFS(PTRef root, vec<type> &flag) const {
    auto index = Idx(logic.getPterm(root).getId());
    flag[index] = type::gray;
    Pterm &t = logic.getPterm(root);
    for (int i = 0; i < t.size(); i++) {
        auto childIndex = Idx(logic.getPterm(t[i]).getId());
        if (flag[childIndex] == type::white) {
            DFS(t[i], flag);
        }
    }
    flag[index] = type::black;
}

void IteManager::iterativeDFS(PTRef root) const {
    vec<PTRef> queue;
    vec<type> flag;
    flag.growTo(logic.getNumberOfTerms());
    queue.push(root);

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        const Pterm &t = logic.getPterm(tr);
        auto index = Idx(t.getId());
        if (flag[index] == type::black) {
            queue.pop();
            continue;
        }

        flag[index] = type::gray;

        bool unprocessed_children = false;

        for (int i = 0; i < t.size(); i++) {
            auto childIndex = Idx(logic.getPterm(t[i]).getId());
            if (flag[childIndex] == type::white) {
                queue.push(t[i]);
                unprocessed_children = true;
            }
        }

        if (unprocessed_children) {
            continue;
        }

        flag[index] = type::black;

        queue.pop();
    }
}

void IteManager::constructSwitchTables(PTRef root) {

    vec<PTRef> queue;
    enum class type { white, gray, black };
    vec<type> flag;
    flag.growTo(logic.getNumberOfTerms());

    queue.push(root);
    while (queue.size() != 0) {
        PTRef tr = queue.last();
        const Pterm &t = logic.getPterm(tr);
        auto index = Idx(t.getId());
        if (flag[index] == type::black) {
            queue.pop();
            continue;
        }

        flag[index] = type::gray;

        bool unprocessed_children = false;

        for (int i = 0; i < t.size(); i++) {
            auto childIndex = Idx(logic.getPterm(t[i]).getId());
            if (flag[childIndex] == type::white) {
                queue.push(t[i]);
                unprocessed_children = true;
            }
        }

        if (unprocessed_children) {
            continue;
        }

        flag[index] = type::black;

        queue.pop();

        if (logic.isIte(tr)) {

            ite_nodes.insert(tr, true);
            assert(!switchTables.has(tr));

            Pterm &ite = logic.getPterm(tr);
            PTRef cond_tr = ite[0];
            PTRef true_tr = ite[1];
            PTRef false_tr = ite[2];

            ite::SwitchTable *true_table = switchTables.getTableOrCreateLeafTable(true_tr);
            ite::SwitchTable *false_table = switchTables.getTableOrCreateLeafTable(false_tr);

            switchTables.createAndStoreTable(tr, cond_tr, true_table, false_table);

        } else {
            // not Ite
            for (int i = 0; i < logic.getPterm(tr).size(); i++) {
                Pterm& t_safe = logic.getPterm(tr);
                if (logic.isIte(t_safe[i]) and !top_level_ites.has(t_safe[i])) {
                    // Term t[i] is an ite which appears as a child of a non-ite.
                    // Therefore its corresponding switch table is stored.
                    top_level_ites.insert(t_safe[i], true);
                    vec<ite::CondValPair> flatSwitches = switchTables.asConstrs(logic, t_safe[i]);
                    for (auto condVal : flatSwitches) {
                        flat_top_level_switches.push(logic.mkImpl(condVal.cond, logic.mkEq(t_safe[i], condVal.val)));
                    }
                }
            }
        }
    }
}

void IteManager::conjoinItes(PTRef root, PTRef& new_root)
{
    PTRef tmp = logic.mkAnd(flat_top_level_switches);
    new_root = logic.mkAnd(tmp, new_root);
}
