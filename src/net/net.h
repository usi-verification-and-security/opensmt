//
//  Created by Matteo Marescotti.
//

#ifndef NET_H
#define NET_H

#include <iostream>
#include <stdlib.h>
#include <string>
#include <stdio.h>
#include <stdlib.h>
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
#include "net.h"
#include "protocol.h"
#include "api/MainSolver.h"
#include "logics/Theory.h"

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

    static void solve(int wpipefd, std::string &osmt2, uint32_t jid);

public:
    WorkerClient();

    void runForever();
};

#endif