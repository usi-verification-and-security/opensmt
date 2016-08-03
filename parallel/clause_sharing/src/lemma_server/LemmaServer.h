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


class LemmaServer : public Server {
private:
    Settings &settings;
    std::map<std::string, std::list<SMTLemma>> lemmas;                            // hash -> lemmas
    std::map<std::string, std::map<std::string, std::list<SMTLemma *>>> solvers;  //hash -> solver -> lemmas
    //TIMEDEBUG
    std::map<std::string, time_t> times;

protected:
    void handle_accept(Socket &);

    void handle_close(Socket &);

    void handle_message(Socket &, std::map<std::string, std::string> &, std::string &);

    void handle_exception(Socket &, SocketException &);

public:

    LemmaServer(Settings &settings) : Server(settings.port), settings(settings) { };
};

#endif //CLAUSE_SHARING_CLAUSESERVER_H
