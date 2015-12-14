//
// Created by Matteo on 10/12/15.
//

#ifndef CLAUSE_SHARING_MAIN_H
#define CLAUSE_SHARING_MAIN_H

#include <iostream>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netdb.h>
#include "api/MainSolver.h"
#include "lib/Thread.h"
#include "lib/Process.h"
#include "lib/Message.h"
#include "hiredis.h"


namespace opensmt {
    extern bool stop;
}


class Settings {
public:
    typedef struct {
        std::string hostname;
        uint16_t port;
    } Address;

    static Settings Default;

    Settings() :
            redis({.hostname=std::string("127.0.0.1"), .port=6379}),
            server({.hostname=std::string("127.0.0.1"), .port=3000}),
            clause_sharing(true) { }

    void load(int argc, char **argv);

    Address redis;
    Address server;
    bool clause_sharing;

};


class _SMTSolver : public SimpSMTSolver {
private:
    std::string channel;
    redisContext *cls_pub;
    redisContext *cls_sub;

    void clausesPublish();

    void clausesUpdate();

public:
    _SMTSolver(std::string &channel, SMTConfig &c, THandler &t);

    ~_SMTSolver();

};


class _Solver : public MainSolver {
private:
    _SMTSolver sat_solver;
    THandler &thandler;

public:
    _Solver(std::string &channel, Theory &t, SMTConfig &c) :
            MainSolver(t, c), thandler(t.getTHandler()), sat_solver(channel, c, thandler) { }

};


class ProcessSolver : public Process {
private:
    std::string osmt2;

protected:
    void main();

public:
    ProcessSolver(std::string &id, std::string &osmt2);

    std::string id;

};


#endif //CLAUSE_SHARING_MAIN_H
