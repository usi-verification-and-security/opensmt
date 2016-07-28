//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_CLAUSESERVER_H
#define CLAUSE_SHARING_CLAUSESERVER_H

#include <map>
#include <vector>
#include "lib/Net.h"
#include "SMTLiteral.h"


class LemmaServer : public Server {
private:
    std::map<std::string, std::vector<SMTLiteral>> lemmas;

protected:
    void handle_accept(Socket &);

    void handle_close(Socket &);

    void handle_message(Socket &, std::map<std::string, std::string> &, std::string &);

    void handle_exception(Socket &, SocketException &);

public:

    LemmaServer(uint16_t port) : Server(port) { };
};

#endif //CLAUSE_SHARING_CLAUSESERVER_H
