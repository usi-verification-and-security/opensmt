//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_CLAUSESERVER_H
#define CLAUSE_SHARING_CLAUSESERVER_H

#include "lib/Net.h"


class ClauseServer : public Server {
public:
    ClauseServer(uint16_t port) : Server(port) { }

protected:
    void handle_accept(Socket &);

    void handle_close(Socket &);

    void handle_message(Socket &, std::map<std::string, std::string> &, std::string &);

    void handle_exception(Socket &, SocketException &);
};

#endif //CLAUSE_SHARING_CLAUSESERVER_H
