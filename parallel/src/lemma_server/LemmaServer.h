//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_CLAUSESERVER_H
#define CLAUSE_SHARING_CLAUSESERVER_H

#include <map>
#include <ctime>
#include "lib/Net.h"
#include "SMTLemma.h"
#include "Settings.h"
#include "Node.h"


class LemmaServer : public Server {
private:
    Settings &settings;
    std::map<std::string, Node *> lemmas;                            // name -> lemmas
    std::map<std::string, std::map<std::string, std::list<SMTLemma *>>> solvers;  // name -> solver -> lemmas
protected:
    void handle_accept(Socket &);

    void handle_close(Socket &);

    void handle_message(Socket &, std::map<std::string, std::string> &, std::string &);

    void handle_exception(Socket &, SocketException &);

public:

    LemmaServer(Settings &settings) : Server(settings.port), settings(settings) { };
};

#endif //CLAUSE_SHARING_CLAUSESERVER_H
