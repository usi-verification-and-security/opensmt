//
//  Created by Matteo Marescotti.
//

#ifndef NET_H
#define NET_H

#include <iostream>
#include <stdlib.h>
#include <string>
#include <stdio.h>
#include <stdint.h>
#include <sys/socket.h>
#include <netdb.h>
#include <unistd.h>
#include <errno.h>
#include <strings.h>
#include <string.h>
#include <thread>
#include <random>
#include <arpa/inet.h>

#include "SolverTypes.h"
#include "hiredis/hiredis.h"
#include "net.h"
#include "protocol.h"
#include <string>

class NetCfg {
public:
    static std::string server_host;
    static uint16_t server_port;

    static std::string signature();

private:
    NetCfg() { };

    NetCfg(NetCfg const &);

    void operator=(NetCfg const &);
};

class FrameSocket {
private:
    int sockfd;

public:
    FrameSocket(int sockfd);

    uint32_t readn(char *buffer, uint32_t length);

    uint32_t read(char **frame);

    uint32_t write(char *frame, uint32_t length);

    int fd() { return this->sockfd; }
};

class WorkerClient {
private:
    FrameSocket *s;
    FrameSocket *rpipe;
    std::thread t;
    uint32_t jid;

    void command(char *frame, uint32_t length);

    static void solve(int wpipefd, char *osmt2filename, uint32_t jid);

public:
    WorkerClient(char *host, uint16_t port);

    void runForever();
};

class CoreSMTSolver;

class Sharing {

public:
    Sharing();

    ~Sharing();

    void clausesPublish(CoreSMTSolver &solver);

    void clausesUpdate(CoreSMTSolver &solver);

    void reset(char *channel);

private:
    redisContext *c_cls_pub;
    redisContext *c_cls_sub;
    char *channel;

    redisContext *connect();

    void flush(redisContext *context);

    static inline void inet_source(int fd, std::string &str);

};

#endif