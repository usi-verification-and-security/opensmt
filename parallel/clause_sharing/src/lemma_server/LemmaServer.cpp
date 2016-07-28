//
// Created by Matteo Marescotti on 02/12/15.
//

#include "LemmaServer.h"
#include "lib/Log.h"


void LemmaServer::handle_accept(Socket &client) {
    Log::log(Log::INFO, "+ " + client.get_remote().toString());
}

void LemmaServer::handle_close(Socket &client) {
    Log::log(Log::INFO, "- " + client.get_remote().toString());
}

void LemmaServer::handle_exception(Socket &client, SocketException &ex) {
    Log::log(Log::WARNING, "Exception from: " + client.get_remote().toString() + ": " + ex.what());
}

void LemmaServer::handle_message(Socket &client,
                                 std::map<std::string, std::string> &header,
                                 std::string &payload) {
    if (header.count("lemmas") == 0 || header.count("hash") == 0)
        return;
    const uint32_t clauses_request = (uint32_t) atoi(header["lemmas"].c_str());
    auto clauses = &this->lemmas[header["hash"]];

    if (header.count("separator") == 1) {
        uint32_t pushed = 0;
        uint32_t n = 0;
        uint32_t s = 0;
        uint32_t e = 0;
        while (true) {
            while (payload[e] != header["separator"][0] && e < payload.size() && e != -1) { e++; }
            if (s == e)
                break;
            SMTLiteral literal(payload.substr(s, e - s));
            auto it = std::find(clauses->begin(), clauses->end(), literal);
            if (it != clauses->end())
                it->increase();
            else {
                pushed++;
                clauses->push_back(literal);
            }
            n++;
            e++;
            s = e;
        }
        Log::log(Log::INFO,
                 client.get_remote().toString() + " push [" + header["lemmas"] + "]\t" +
                 std::to_string(n) +
                 "\t(" + std::to_string(pushed) + "\tfresh, " + std::to_string(n - pushed) + "\tpresent)");
    }
    else {
        header["separator"] = "\n";
        payload.clear();
        uint32_t n = 0;
        if (this->lemmas.count(header["hash"])) {
            std::sort(clauses->begin(), clauses->end());
            for (auto literal = clauses->rbegin(); literal != clauses->rend(); ++literal) {
                if (n >= clauses_request)
                    break;
                payload += literal->smtlib;
                payload += "\n";
                n++;
            }
        }
        header["lemmas"] = std::to_string(n);
        client.write(header, payload);
        Log::log(Log::INFO,
                 client.get_remote().toString() + " pull [" + header["lemmas"] + "]\t" + std::to_string(n));
    }
}
