//
// Created by Matteo on 22/07/16.
//

#ifndef CLAUSE_SHARING_SOLVERSERVER_H
#define CLAUSE_SHARING_SOLVERSERVER_H

#include <ctime>
#include "lib/Net.h"
#include "SolverProcess.h"


class SolverServer : public Server {
private:
    void stop_solver();

    void log(uint8_t, std::string);

    bool check_header(std::map<std::string, std::string> &);

    Settings &settings;
    Socket &server;
    SolverProcess *solver;
    //TIMEDEBUG
    std::map<std::string, time_t> start;
protected:
    void handle_close(Socket &);

    void handle_exception(Socket &, SocketException &);

    void handle_message(Socket &, std::map<std::string, std::string> &, std::string &);

public:
    SolverServer(Settings &, Socket &);
};


#endif //CLAUSE_SHARING_SOLVERSERVER_H
