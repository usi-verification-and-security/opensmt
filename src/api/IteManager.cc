//
// Created by prova on 04.08.20.
//

#include "IteManager.h"
#include "Logic.h"

int ite::IteDagNode::id_count = 0;

ite::IteDagNode* ite::IteDag::newNode(PTRef val) {
    assert(not nodes.has(val));
    nodePointers.push(new ite::IteDagNode(val, val));
    nodes.insert(val, nodePointers.last());
    return nodePointers.last();
}

ite::IteDagNode* ite::IteDag::newNode(PTRef tr, PTRef cond, ite::IteDagNode *true_node, ite::IteDagNode *false_node)
{
    assert(not nodes.has(tr));
    nodePointers.push(new ite::IteDagNode(tr, cond, true_node, false_node));
    nodes.insert(tr, nodePointers.last());
    return nodePointers.last();
}

ite::CondValPair ite::IteDag::getPathConstr(const IteDagNode *leaf, std::map<const IteDagNode*,IteParentRecord> &parents, Logic &logic) {
    assert(leaf->getCond() == PTRef_Undef);
    assert(leaf->getVal() != PTRef_Undef);
    assert(not logic.isIte(leaf->getVal()));

    vec<std::pair<PTRef,IteParentRecord*>> path;
    const IteDagNode *node = leaf;

    PTRef shortcutFormula = PTRef_Undef;

    while (parents.find(node) != parents.end()) {
        auto &parent = parents.at(node);
        node = parent.getNode();
        assert(node->getCond() != PTRef_Undef);
        assert(node->getVal() == PTRef_Undef);
        lbool sign = parent.getSign();
        PTRef tr = node->getCond();
        path.push(sign == l_True ? std::pair<PTRef,IteParentRecord*>{tr, &parent} : std::pair<PTRef,IteParentRecord*>{logic.mkNot(tr), &parent});
        shortcutFormula = parent.getPathFormula();

        if (shortcutFormula != PTRef_Undef) {
            break;
        }
    }
    if (shortcutFormula != PTRef_Undef) {
//        PTRef cond = logic.getTerm_true();
        for (int i = path.size() - 1; i >= 0; i--) {
//            auto condAndRecord = path[i];
//            PTRef cond = condAndRecord.first;
//            IteParentRecord *pr = condAndRecord.second;
//            pr->setPathFormula();
        }
    }
    std::cout << "path length: " << path.size() << std::endl;
//    return {logic.mkAnd(path), leaf->getVal()};
    return {logic.getTerm_true(), leaf->getVal()};
}

vec<ite::CondValPair> ite::IteDag::asConstrs(Logic &logic, PTRef source) const {
    assert(nodes.has(source));
    assert(logic.isIte(source));
    std::map<const IteDagNode*,IteParentRecord> parents;
    vec<const IteDagNode*> queue;

    queue.push(nodes[source]);

    vec<CondValPair> constrs;

    while (queue.size() != 0) {
        const IteDagNode *node = queue.last();
        queue.pop();

        bool isLeaf = true;
        for (lbool child_sign : {l_True, l_False}) {
            const IteDagNode *child = (child_sign == l_True ? node->getTrueChild() : node->getFalseChild());
            if (child != nullptr) {
                queue.push(child);
                parents[child] = IteParentRecord(child_sign, node);
                isLeaf = false;
            }
        }
        if (isLeaf) {
            auto row = getPathConstr(node, parents, logic);
            constrs.push(row);
        }
    }
    return constrs;
}

ite::IteDag ite::IteDag::getReachableSubGraph(const Logic &logic, PTRef root) {
    IteDag dag;
    vec<const IteDagNode*> queue;
    enum class type { white, gray, black };
    vec<type> flag;
    flag.growTo(IteDagNode::getIdCount()+1);
    IteDagNode *rootNode = nodes[root];
    queue.push(rootNode);

    while (queue.size() > 0) {
        const IteDagNode &el = *queue.last();
        if (flag[el.getId()] == type::black) {
            queue.pop();
            continue;
        }

        flag[el.getId()] = type::gray;
        bool unprocessed_children = false;
        for (const IteDagNode *child : {el.getFalseChild(), el.getTrueChild()}) {
            if (child != nullptr && flag[child->getId()] == type::white) {
                queue.push(child);
                unprocessed_children = true;
            }
        }

        if (unprocessed_children) {
            continue;
        }

        flag[el.getId()] = type::black;

        queue.pop();

        PTRef term = el.getTerm();
        if (logic.isIte(term)) {
            assert(el.getTrueChild() != nullptr);
            assert(el.getFalseChild() != nullptr);
            ite::IteDagNode *true_node = dag.getNodeOrCreateLeafNode(term, el.getTrueChild()->getTerm());
            ite::IteDagNode *false_node = dag.getNodeOrCreateLeafNode(term, el.getFalseChild()->getTerm());
            dag.createAndStoreNode(term, el.getCond(), true_node, false_node);
        } else {
            for (int i = 0; i < logic.getPterm(term).size(); i++) {
                PTRef c = logic.getPterm(term)[i];
                if (logic.isIte(c) and isTopLevelIte(c)) {
                    dag.addTopLevelIte(c);
                }
            }
        }
    }
    return dag;
}

ite::IteDag IteManager::constructIteDag(PTRef root, const Logic &logic) {

    ite::IteDag dag;

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

            dag.addItePTRef(tr);

            const Pterm &ite = logic.getPterm(tr);
            PTRef cond_tr = ite[0];
            PTRef true_tr = ite[1];
            PTRef false_tr = ite[2];
            std::cout << "Found Ite" << std::endl;
            {
                auto t = ite::timer("ite");
                ite::IteDagNode *true_node = dag.getNodeOrCreateLeafNode(tr, true_tr);
                ite::IteDagNode *false_node = dag.getNodeOrCreateLeafNode(tr, false_tr);

                dag.createAndStoreNode(tr, cond_tr, true_node, false_node);
            }

        } else { // not Ite
            std::cout << "Found a non-Ite" << std::endl;
            for (int i = 0; i < t.size(); i++) {
                if (logic.isIte(t[i]) and !dag.isTopLevelIte(t[i])) {
                    // Term t[i] is an ite which appears as a child of a non-ite.
                    // We store this term for an expansion into a switch.
                    dag.addTopLevelIte(t[i]);
                }
            }
        }
    }
    return dag;
}

void IteManager::traverseTopLevelItes() {
    vec<PTRef> ites = iteDag.getTopLevelItes();
    int i = 0;
    for (auto tl_ite : ites) {
        auto t = ite::timer("as Constrs");
        ite::IteDag subDag = iteDag.getReachableSubGraph(logic, tl_ite);
        std::string name("subgraph_");
        name += std::to_string(i++) + ".dot";
        printDagToFile(name, subDag);
    }
}

void IteManager::conjoinItes(PTRef root, PTRef& new_root)
{
    PTRef tmp = logic.mkAnd(flat_top_level_switches);
    new_root = logic.mkAnd(tmp, new_root);
}

