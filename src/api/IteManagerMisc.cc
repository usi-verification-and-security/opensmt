//
// Created by prova on 02.09.20.
//
#include "IteManager.h"
#include <fstream>

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

void IteManager::printDagToFile(const std::string &fname, const ite::IteDag &dag) {
    std::fstream fs;
    fs.open(fname, std::fstream::out);
    fs << dag.getDagAsStream().rdbuf();
    fs.close();
}

std::stringstream ite::IteDag::getDagAsStream() const {
    std::stringstream annotations;
    std::stringstream edges;
    std::stringstream out;
    auto &nodes = getIteDagNodes();
    for (const ite::IteDagNode *node : nodes) {
        if (isTopLevelIte(node->getTerm())) {
            annotations << node->getId() << " [shape=box]" << endl;
        }
        if (node->getTrueChild() != nullptr) {
            edges << " " << node->getId() << " -> " << node->getTrueChild()->getId() << ";" << std::endl;
        }
        if (node->getFalseChild() != nullptr) {
            edges << " " << node->getId() << " -> " << node->getFalseChild()->getId() << ";" << std::endl;
        }
    }
    out << "digraph G {" << std::endl;
    out << annotations.rdbuf();
    std::cout << out.rdbuf();
    out << edges.rdbuf();
    out << "}" << std::endl;
    out << std::flush;
    return out;
}