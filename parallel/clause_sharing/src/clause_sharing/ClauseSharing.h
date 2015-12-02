//
// Created by Matteo on 02/12/15.
//

#ifndef CLAUSE_SHARING_HEURISTIC_H
#define CLAUSE_SHARING_HEURISTIC_H


#include <thread>
#include <iostream>
#include <string.h>
#include "Sort.h"
#include "settings/settings.h"
#include "net/protocol.h"

extern "C" {
#include <hiredis.h>
}

class ClauseSharing {

private:
    std::thread *thread;
    std::string channel;
    redisContext *context_pub;
    redisContext *context_sub;

    static redisContext *Connect(const char *hostname, int port);

    void heuristic();

public:
    ClauseSharing(const char *channel);

    void Start();

    void Stop();

};


#endif //CLAUSE_SHARING_HEURISTIC_H
