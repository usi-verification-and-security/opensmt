//
// Created by Matteo Marescotti on 02/12/15.
//

#include <iostream>
#include <fstream>
#include <algorithm>
#include "lib/Log.h"
#include "LemmaServer.h"


void LemmaServer::handle_accept(Socket &client) {
    Log::log(Log::INFO, "+ " + client.get_remote().toString());
}

void LemmaServer::handle_close(Socket &client) {
    for (auto pair:this->solvers) {
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
    if (header.count("name") == 0 || header.count("lemmas") == 0)
        return;

    const uint32_t clauses_request = (uint32_t) atoi(header["lemmas"].c_str());
    std::list<SMTLemma> *lemmas = &this->lemmas[header["name"]];

    if (header.count("separator") == 1) {
        std::list<SMTLemma *> *lemmas_solver = &this->solvers[header["name"]][client.get_remote().toString()];
        uint32_t pushed = 0;
        uint32_t n = 0;
        uint32_t s = 0;
        uint32_t e = 0;
        while (true) {
            while (payload[e] != header["separator"][0] && e < payload.size() && e != (uint32_t) -1) { e++; }
            if (s == e)
                break;
            SMTLemma lemma(payload.substr(s, e - s));
            auto it = std::find(lemmas->begin(), lemmas->end(), lemma);
            if (it != lemmas->end()) {
                it->increase();
                lemmas_solver->push_back(&*it);
            }
            else {
                pushed++;
                lemmas->push_back(lemma);
                lemmas_solver->push_back(&lemmas->back());
            }
            n++;
            e++;
            s = e;
        }
        Log::log(Log::INFO,
                 header["name"] + " " + client.get_remote().toString() +
                 " push [" + std::to_string(clauses_request) + "]\t" +
                 std::to_string(n) +
                 "\t(" + std::to_string(pushed) + "\tfresh, " + std::to_string(n - pushed) + "\tpresent)");
    }
    else {
        payload.clear();
        uint32_t n = 0;
        std::list<SMTLemma *> *lemmas_solver = NULL;
        if (header.count("exclude") && this->solvers[header["name"]].count(header["exclude"])) {
            lemmas_solver = &this->solvers[header["name"]][header["exclude"]];
        }
        if (this->lemmas.count(header["name"])) {
            lemmas->sort();
            for (auto lemma = lemmas->rbegin(); lemma != lemmas->rend(); ++lemma) {
                if (n >= clauses_request)
                    break;
                if (lemmas_solver != NULL) {
                    auto fdd = std::find(lemmas_solver->begin(), lemmas_solver->end(), &*lemma);
                    if (fdd != lemmas_solver->end())
                        continue;
                    lemmas_solver->push_back(&*lemma);
                }
                payload += lemma->smtlib;
                payload += "\n";
                n++;
            }
        }
        header["lemmas"] = std::to_string(n);
        header["separator"] = "\n";
        try {
            client.write(header, payload);
        }
        catch (SocketException ex) { return; }
        Log::log(Log::INFO,
                 header["name"] + " " + client.get_remote().toString() +
                 " pull [" + std::to_string(clauses_request) + "]\t" +
                 std::to_string(n));
    }
}
