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
#include "lib/Message.h"


class Settings {
public:
    typedef struct {
        std::string hostname;
        uint16_t port;
    } Address;

    static Settings Default;

    Settings() :
            redis({.hostname=std::string("127.0.0.1"), .port=6379}), server({.hostname=std::string("127.0.0.1"), .port=3000}) { }

    void load(int argc, char **argv);

    Address redis;
    Address server;

};


class _SMTSolver : public SimpSMTSolver {
private:
    std::string channel;

    void clausesPublish();

    void clausesUpdate();

public:
    _SMTSolver(std::string &channel, SMTConfig &c, THandler &t) :
            SimpSMTSolver(c, t), channel(channel) { }

};


class _Solver : public MainSolver {
private:
    _SMTSolver sat_solver;
    THandler &thandler;

public:
    _Solver(std::string &channel, Theory &t, SMTConfig &c) :
            MainSolver(t, c), thandler(t.getTHandler()), sat_solver(channel, c, thandler) { }

};


class ThreadSolver : public Thread {
private:
    std::string channel;
    std::string osmt2;

protected:
    void main();

    inline void solve();

public:
    ThreadSolver(std::string &channel, std::string &osmt2);

    ~ThreadSolver();

    sstat status;
    char *msg;

};


#endif //CLAUSE_SHARING_MAIN_H
