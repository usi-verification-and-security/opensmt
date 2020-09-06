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

void ite::IteDag::annotateWithParentInfo(const IteDagNode *root) {
    vec<const IteDagNode*> queue;
    vec<type> flag;
    flag.growTo(IteDagNode::getIdCount() + 1);
    parents[root] = std::set<std::pair<const IteDagNode*,lbool>>();
    queue.push(root);
    while (queue.size() != 0) {
        const IteDagNode &el = *queue.last();
        if (flag[el.getId()] == type::black) {
            queue.pop();
            continue;
        }
        flag[el.getId()] = type::gray;

        bool unprocessed_children = false;

        for (lbool childPolarity : { l_False, l_True }) {
            const IteDagNode *child = childPolarity == l_False ? el.getFalseChild() : el.getTrueChild();
            if (child != nullptr) {
                if (parents.find(child) == parents.end()) {
                    parents[child] = std::set<std::pair<const IteDagNode *, lbool>>();
                }
                if (flag[child->getId()] == type::white) {
                    unprocessed_children = true;
                    queue.push(child);
                }
                parents[child].insert({&el, childPolarity});
            }
            else {
                leaves.insert(&el);
            }
        }

        if (unprocessed_children) {
            continue;
        }

        flag[el.getId()] = type::black;
        queue.pop();
    }
}

ite::IteDag ite::IteDag::getReachableSubGraph(const Logic &logic, PTRef root) {
    IteDag dag;
    vec<const IteDagNode*> queue;
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
            ite::IteDagNode *true_node = dag.getNodeOrCreateLeafNode(el.getTrueChild()->getTerm());
            ite::IteDagNode *false_node = dag.getNodeOrCreateLeafNode(el.getFalseChild()->getTerm());
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

vec<ite::CondValPair> ite::IteDag::getCondValPairs(Logic& logic) const {
    // Reverse traversal starting from leaves
    std::map<const IteDagNode*, PTRef> dagNodeToPTRef;
    vec<const IteDagNode*> queue;
    for (auto root : leaves) {
        queue.push(root);
    }
    vec<type> flag;
    flag.growTo(IteDagNode::getIdCount()+1);
    vec<CondValPair> switches;

    while (queue.size() != 0) {
        const IteDagNode &el = *queue.last();

        if (flag[el.getId()] == type::black) {
            queue.pop();
            continue;
        }

        bool unprocessed_parents = false;
        for (const auto &parentAndPolarity : parents.at(&el)) {
            auto parent = parentAndPolarity.first;
            if (flag[parent->getId()] == type::white) {
                flag[parent->getId()] = type::gray;
                queue.push(parent);
                unprocessed_parents = true;
            }
        }

        if (unprocessed_parents) {
            continue;
        }

        flag[el.getId()] = type::black;
        queue.pop();

        if (dagNodeToPTRef.find(&el) == dagNodeToPTRef.end()) {
            auto &myParents = parents.at(&el);
            vec<PTRef> parentConditions;
            if (myParents.empty()) {
                parentConditions.push(logic.getTerm_true());
            } else {
                for (auto &nodeAndPolarity : myParents) {
                    PTRef cond = nodeAndPolarity.first->getCond();
                    lbool pol = nodeAndPolarity.second;
                    PTRef parentCondition = dagNodeToPTRef.at(nodeAndPolarity.first);
                    PTRef edgeCondition = pol == l_True ? cond : logic.mkNot(cond);
                    parentConditions.push(logic.mkAnd(parentCondition, edgeCondition));
                }
            }

            PTRef pathCondition = logic.mkOr(parentConditions);
            dagNodeToPTRef[&el] = pathCondition;

            if (el.getCond() == PTRef_Undef) {
                // A value node
                assert(el.getVal() != PTRef_Undef and el.getTrueChild() == nullptr and el.getFalseChild() == nullptr);
                switches.push_m(CondValPair(pathCondition, el.getVal()));
            }
        }
    }

    return switches;
}

ite::IteDag IteManager::constructIteDag(PTRef root, const Logic &logic) {

    ite::IteDag dag;

    vec<PTRef> queue;
    vec<type> flag;
    flag.growTo(logic.getNumberOfTerms());

    queue.push(root);
    while (queue.size() != 0) {
        PTRef tr = queue.last();
        const Pterm &t = logic.getPterm(tr);
        auto index = Idx(t.getId());
        if (flag[index] == ite::type::black) {
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
            {
                ite::IteDagNode *true_node = dag.getNodeOrCreateLeafNode(true_tr);
                ite::IteDagNode *false_node = dag.getNodeOrCreateLeafNode(false_tr);

                dag.createAndStoreNode(tr, cond_tr, true_node, false_node);
            }

        } else { // not Ite
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

    for (auto tl_ite : ites) {
//        auto t = ite::timer("as Constrs");
        ite::IteDag subDag = iteDag.getReachableSubGraph(logic, tl_ite);
        PTRef switch_tr = makeSwitch(tl_ite);
        switches.push(switch_tr);
    }
}

PTRef IteManager::makeSwitch(PTRef root) {
    assert(isIteVar(root));
    ite::IteDag dag = iteDag.getReachableSubGraph(logic, root);
    const ite::IteDagNode* root_node = dag.getNode(root);
    dag.annotateWithParentInfo(root_node);
    vec<ite::CondValPair> root_switches = dag.getCondValPairs(logic);
    vec<PTRef> cases;
    for (auto condVal : root_switches) {
//        std::cout << logic.pp(condVal.cond) << " -> " << logic.pp(condVal.val) << std::endl;
        cases.push(logic.mkImpl(condVal.cond, logic.mkEq(root, condVal.val)));
    }
    return logic.mkAnd(cases);
}



