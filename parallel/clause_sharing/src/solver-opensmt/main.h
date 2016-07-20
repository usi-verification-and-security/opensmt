//
// Created by Matteo on 10/12/15.
//

#ifndef SOLVER_OPENSMT_MAIN_H
#define SOLVER_OPENSMT_MAIN_H

#include <iostream>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netdb.h>
#include "api/MainSolver.h"
#include "lib/Thread.h"
#include "lib/Process.h"
#include "lib/Net.h"


namespace opensmt {
    extern bool stop;
}


class Settings {
public:
    static Settings Default;

    Settings();

    void load(int, char **);

    Address server;
    Address clause_sharing;
};


//class _SMTSolver : public SimpSMTSolver {
//private:
//    std::string name;
//    std::string hash;
//
//    void inline clausesPublish();
//
//    void inline clausesUpdate();
//
//public:
//    _SMTSolver(Settings &s, std::string &name, std::string &hash, SMTConfig &c, THandler &t);
//
//    ~_SMTSolver();
//
//};


class ClauseSharingThread : public Thread {
private:
    class ClauseSharingServer : public Server {
    public:
        ClauseSharingServer(Socket &socket) : Server(socket) { }

        void handle_message(Socket &, std::map<std::string, std::string> &, std::string &);
    };

    Settings &settings;
    ClauseSharingServer *server;

protected:
    void main();

public:
    ClauseSharingThread(Settings &);

    ~ClauseSharingThread();

};

//class ProcessSolver : public Process {
//private:
//    std::string osmt2;
//    std::string channel;
//    Settings settings;
//
//protected:
//    void main();
//
//public:
//    ProcessSolver(Settings &settings, std::string &channel, std::string &osmt2);
//
//};


#endif //SOLVER_OPENSMT_MAIN_H
