//
// Created by Matteo on 11/08/16.
//

#ifndef CLAUSE_SERVER_NODE_H
#define CLAUSE_SERVER_NODE_H

#include <string>
#include <list>
#include <vector>


class Node {
public:
    std::list<SMTLemma *> lemmas;
    std::vector<Node *> children;

    Node() { }

    ~Node() {
        for (auto lemma:this->lemmas) {
            delete (lemma);
        }
        for (auto child:this->children) {
            delete (child);
        }
    }

//    std::string toString(int i = 0) {
//        auto r = std::string(i, '\t');
//        for (auto l : this->lemmas) {
//            r.append(l->smtlib + ", ");
//        }
//        r.append("\n");
//        for (auto c : this->children) {
//            r.append(c->toString(i + 1));
//        }
//        return r;
//    }
};

#endif //CLAUSE_SERVER_NODE_H
