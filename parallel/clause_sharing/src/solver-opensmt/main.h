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

    void inline clausesPublish();

    void inline clausesUpdate();

public:
    _SMTSolver(Settings &s, std::string &channel, SMTConfig &c, THandler &t);

    ~_SMTSolver();

};

//
//class _Solver : public MainSolver {
//protected:
////    THandler &thandler;
////    Tseitin ts;
////    Logic &logic;
////    TermMapper &tmap;
//
//public:
//    _Solver(Settings &s, std::string &channel, Theory &t, SMTConfig &c, _SMTSolver *solver) :
//            MainSolver(t,c,solver)
//
//};


class ProcessSolver : public Process {
private:
    std::string osmt2;
    std::string channel;
    Settings settings;

protected:
    void main();

public:
    ProcessSolver(Settings &settings, std::string &channel, std::string &osmt2);

};


#endif //CLAUSE_SHARING_MAIN_H
