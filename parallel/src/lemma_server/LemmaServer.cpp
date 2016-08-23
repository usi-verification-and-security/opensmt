//
// Created by Matteo Marescotti on 02/12/15.
//

#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include "lib/lib.h"
#include "lib/Log.h"
#include "lib/Exception.h"
#include "LemmaServer.h"


LemmaServer::LemmaServer(Settings &settings) :
        Server(settings.port),
        settings(settings),
        server(NULL),
        db(NULL) {
    if (this->settings.server.port > 0) {
        this->server = new Socket(this->settings.server);
        std::map<std::string, std::string> header;
        header["lemmas"] = ":" + std::to_string(this->settings.port);
        this->server->write(header, "");
        this->add_socket(this->server);
    }
    if (this->settings.db_filename.size() > 0) {
        this->db = new SQLite3(this->settings.db_filename);
        this->db->exec("CREATE TABLE IF NOT EXISTS Lemma"
                               "(id INTEGER PRIMARY KEY, name TEXT, node TEXT, score INTEGER, smtlib TEXT);");
    }
};

LemmaServer::~LemmaServer() {
    if (this->db)
        delete this->db;
}


void LemmaServer::handle_accept(Socket &client) {
    Log::log(Log::INFO, "+ " + client.get_remote().toString());
}


void LemmaServer::handle_close(Socket &client) {
    if (&client == this->server)
        throw Exception("server connection closed.");
    for (auto &pair:this->solvers) {
        if (this->solvers[pair.first].count(client.get_remote().toString())) {
            this->solvers[pair.first].erase(client.get_remote().toString());
        }
    }
    Log::log(Log::INFO, "- " + client.get_remote().toString());
}


void LemmaServer::handle_exception(Socket &client, SocketException &ex) {
    Log::log(Log::ERROR, "Exception from: " + client.get_remote().toString() + ": " + ex.what());
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
    split(header["node"].substr(1, header["node"].size() - 2), ",", [&node_path](std::string &node_index) {
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

    if (clauses_request == 0) {
        Log::log(Log::INFO,
                 header["name"] + header["node"] + " " + client.get_remote().toString() +
                 " clear");
        Node *node_remove = node_path.back();
        node_path.pop_back();
        if (node_path.size() > 0) {
            std::replace(node_path.back()->children.begin(),
                         node_path.back()->children.end(),
                         node_remove,
                         new Node);
        }
        else {
            if (this->settings.clear_lemmas)
                this->lemmas.erase(header["name"]);
        }
        delete node_remove;
        return;
    }

    if (header.count("separator") == 1) {
        std::list<Lemma *> *lemmas = &node_path.back()->lemmas;
        std::list<Lemma *> *lemmas_solver = &this->solvers[header["name"]][client.get_remote().toString()];

        uint32_t pushed = 0;
        uint32_t n = 0;
        split(payload, header["separator"], [&](std::string &smtlib) {
            if (smtlib.size() == 0)
                return;
            auto it = std::find_if(lemmas->begin(), lemmas->end(), [&smtlib](const Lemma *other) {
                return other->smtlib == smtlib;
            });
            if (it != lemmas->end()) {
                (*it)->increase();
                lemmas_solver->push_back(*it);
                if (this->db) {
                    sqlite3_stmt *stmt = this->db->prepare(
                            "UPDATE Lemma SET score=? WHERE name=? AND node=? AND smtlib=?;");
                    sqlite3_bind_int(stmt, 1, (*it)->get_score());
                    sqlite3_bind_text(stmt, 2, header["name"].c_str(), -1, SQLITE_STATIC);
                    sqlite3_bind_text(stmt, 3, header["node"].c_str(), -1, SQLITE_STATIC);
                    sqlite3_bind_text(stmt, 4, (*it)->smtlib.c_str(), -1, SQLITE_STATIC);
                    this->db->exec(stmt);
                    this->db->finalize(stmt);
                }
            }
            else {
                Lemma *lemma = new Lemma(smtlib);
                pushed++;
                lemmas->push_back(lemma);
                lemmas_solver->push_back(lemmas->back());
                if (this->db) {
                    sqlite3_stmt *stmt = this->db->prepare(
                            "INSERT INTO Lemma (name,node,score,smtlib) VALUES(?,?,?,?);");
                    sqlite3_bind_text(stmt, 1, header["name"].c_str(), -1, SQLITE_STATIC);
                    sqlite3_bind_text(stmt, 2, header["node"].c_str(), -1, SQLITE_STATIC);
                    sqlite3_bind_int(stmt, 3, lemma->get_score());
                    sqlite3_bind_text(stmt, 4, lemma->smtlib.c_str(), -1, SQLITE_STATIC);
                    this->db->exec(stmt);
                    this->db->finalize(stmt);
                }
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
        std::list<Lemma *> *lemmas = new std::list<Lemma *>();
        std::list<Lemma *> *lemmas_solver = NULL;

        if (header.count("exclude") && this->solvers[header["name"]].count(header["exclude"])) {
            lemmas_solver = &this->solvers[header["name"]][header["exclude"]];
        }

        for (auto node:node_path) {
            lemmas->merge(std::list<Lemma *>(node->lemmas));
        }
        lemmas->sort(Lemma::compare);

        payload.clear();
        uint32_t n = 0;
        for (auto lemma = lemmas->rbegin(); lemma != lemmas->rend(); ++lemma) {
            if (n >= clauses_request)
                break;
            if (lemmas_solver != NULL) {
                auto it = std::find_if(lemmas_solver->begin(), lemmas_solver->end(), [&lemma](const Lemma *other) {
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


