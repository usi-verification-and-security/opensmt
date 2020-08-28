//
// Created by prova on 04.08.20.
//

#include "IteManager.h"
#include "Logic.h"

ite::SwitchRow ite::SwitchRow::prepend(PtAsgn constr) const {
    SwitchRow row(value);
    row.constrs.growTo(constrs.size() + 1);
    row.constrs[0] = constr;
    for (int i = 1; i < row.constrs.size(); i++) {
        row.constrs[i] = constrs[i-1];
    }
    return row;
}

ite::SwitchTable::SwitchTable(PTRef cond, const SwitchTable &true_table, const SwitchTable &false_table) {
    for (const auto &row : true_table.rows) {
        rows.push_m(row.prepend({cond, l_True}));
    }
    for (const auto &row : false_table.rows) {
        rows.push_m(row.prepend({cond, l_False}));
    }
}

PTRef ite::SwitchTable::asConstrs(Logic &logic, PTRef target) const {
    vec<PTRef> impls;
    for (int i = 0; i < rows.size(); i++) {
        PTRef conj = logic.getTerm_true();
        const SwitchRow &row = rows[i];
        for (PtAsgn asgn : row.constrs) {
            conj = logic.mkAnd(conj, asgn.sgn == l_True ? asgn.tr : logic.mkNot(asgn.tr));
        }
        PTRef eq = logic.mkEq(target, row.value);
        impls.push(logic.mkImpl(conj, eq));
    }
    return logic.mkAnd(impls);
}

void IteManager::constructSwitchTables(PTRef root) {

    vec<PTRef> queue;
    enum class type { unknown, processed};
    vec<type> flag;
    flag.growTo(logic.getNumberOfTerms());
    queue.push(root);
    while (queue.size() != 0) {
        PTRef tr = queue.last();
        const Pterm &t = logic.getPterm(tr);
        auto index = Idx(t.getId());
        if (flag[index] == type::processed) {
            queue.pop();
            continue;
        }

        bool unprocessed_children = false;

        for (int i = 0; i < t.size(); i++) {
            auto childIndex = Idx(logic.getPterm(t[i]).getId());
            if (flag[childIndex] != type::processed) {
                queue.push(t[i]);
                unprocessed_children = true;
            }
        }

        if (unprocessed_children) {
            continue;
        }

        queue.pop();

        if (logic.isIte(tr)) {

            ite_nodes.insert(tr, true);
            assert(!switchTables.has(tr));

            Pterm &ite = logic.getPterm(tr);
            PTRef cond_tr = ite[0];
            PTRef true_tr = ite[1];
            PTRef false_tr = ite[2];

            ite::SwitchTable *true_table = switchTables.getOrCreateSimpleTable(true_tr);
            ite::SwitchTable *false_table = switchTables.getOrCreateSimpleTable(false_tr);

            switchTables.createAndStoreTable(tr, cond_tr, true_table, false_table);

        } else {
            // not Ite
            for (int i = 0; i < t.size(); i++) {
                if (logic.isIte(t[i]) and !top_level_ites.has(t[i])) {
                    // Term t[i] is an ite which appears as a child of a non-ite.
                    // Therefore its corresponding switch table is stored.
                    top_level_ites.insert(t[i], true);
                    const auto table = switchTables.getTable(t[i]);
                    PTRef flatSwitches = table->asConstrs(logic, t[i]);
                    flat_top_level_switches.push(flatSwitches);
                }
            }
        }
        flag[index] = type::processed;
    }
}

void IteManager::conjoinItes(PTRef root, PTRef& new_root)
{
    PTRef tmp = logic.mkAnd(flat_top_level_switches);
    new_root = logic.mkAnd(tmp, new_root);
}
