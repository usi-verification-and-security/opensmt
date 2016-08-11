//
// Created by Matteo Marescotti on 02/12/15.
//

#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include "lib/lib.h"
#include "lib/Log.h"
#include "LemmaServer.h"


void LemmaServer::handle_accept(Socket &client) {
    Log::log(Log::INFO, "+ " + client.get_remote().toString());
}

void LemmaServer::handle_close(Socket &client) {
    for (auto &pair:this->solvers) {
        if (this->solvers[pair.first].count(client.get_remote().toString())) {
            this->solvers[pair.first].erase(client.get_remote().toString());
        }
    }
    Log::log(Log::INFO, "- " + client.get_remote().toString());
}

void LemmaServer::handle_exception(Socket &client, SocketException &ex) {
    Log::log(Log::WARNING, "Exception from: " + client.get_remote().toString() + ": " + ex.what());
}

void LemmaServer::handle_message(Socket &client,
                                 std::map<std::string, std::string> &header,
                                 std::string &payload) {
    if (header.count("name") == 0 || header.count("node") == 0 || header.count("lemmas") == 0)
        return;

    if (this->lemmas.count(header["name"]) != 1) {
        this->lemmas[header["name"]] = new Node;
    }

    if (header["node"].size() < 2)
        return;

    uint32_t clauses_request = 0;
    try {
        clauses_request = (uint32_t) stoi(header["lemmas"]);
    } catch (std::invalid_argument &ex) {
        return;
    }

    std::vector<Node *> node_path;
    node_path.push_back(this->lemmas[header["name"]]);
    std::string node_indexes = header["node"].substr(1, header["node"].size() - 2);
    split(node_indexes, ",", [&node_path](std::string &node_index) {
        int index;
        try {
            index = stoi(node_index);
            if (index < 0)
                throw std::invalid_argument("negative index");
        } catch (std::invalid_argument &ex) {
            return;
        }
        while ((unsigned) index >= node_path.back()->children.size()) {
            node_path.back()->children.push_back(new Node);
        }
        node_path.push_back(node_path.back()->children[index]);
    });

    if (header.count("separator") == 1) {
        std::list<SMTLemma *> *lemmas = &node_path.back()->lemmas;
        std::list<SMTLemma *> *lemmas_solver = &this->solvers[header["name"]][client.get_remote().toString()];

        uint32_t pushed = 0;
        uint32_t n = 0;
        split(payload, header["separator"], [&](std::string &smtlib) {
            auto it = std::find_if(lemmas->begin(), lemmas->end(), [&smtlib](const SMTLemma *other) {
                return other->smtlib == smtlib;
            });
            if (it != lemmas->end()) {
                (*it)->increase();
                lemmas_solver->push_back(*it);
            }
            else {
                SMTLemma *lemma = new SMTLemma(smtlib);
                pushed++;
                lemmas->push_back(lemma);
                lemmas_solver->push_back(lemmas->back());
            }
            n++;
        });

        Log::log(Log::INFO,
                 header["name"] + header["node"] + " " + client.get_remote().toString() +
                 " push [" + std::to_string(clauses_request) + "]\t" +
                 std::to_string(n) +
                 "\t(" + std::to_string(pushed) + "\tfresh, " + std::to_string(n - pushed) + "\tpresent)");

    }
    else {
        std::list<SMTLemma *> *lemmas = new std::list<SMTLemma *>();
        std::list<SMTLemma *> *lemmas_solver = NULL;

        if (header.count("exclude") && this->solvers[header["name"]].count(header["exclude"])) {
            lemmas_solver = &this->solvers[header["name"]][header["exclude"]];
        }

        for (auto node:node_path) {
            lemmas->merge(std::list<SMTLemma *>(node->lemmas));
        }
        lemmas->sort(SMTLemma::compare);

        payload.clear();
        uint32_t n = 0;
        for (auto lemma = lemmas->rbegin(); lemma != lemmas->rend(); ++lemma) {
            if (n >= clauses_request)
                break;
            if (lemmas_solver != NULL) {
                auto it = std::find_if(lemmas_solver->begin(), lemmas_solver->end(), [&lemma](const SMTLemma *other) {
                    return other->smtlib == (*lemma)->smtlib;
                });
                if (it != lemmas_solver->end())
                    continue;
                lemmas_solver->push_back(*lemma);
            }
            payload += (*lemma)->smtlib;
            payload += "\n";
            n++;
        }
        header["lemmas"] = std::to_string(n);
        header["separator"] = "\n";
        try {
            client.write(header, payload);
        }
        catch (SocketException ex) { return; }
        Log::log(Log::INFO,
                 header["name"] + header["node"] + " " + client.get_remote().toString() +
                 " pull [" + std::to_string(clauses_request) + "]\t" +
                 std::to_string(n));
    }
}
