//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_HEURISTIC_H
#define CLAUSE_SHARING_HEURISTIC_H

#include <iostream>
#include "Sort.h"
#include "lib/Thread.h"
#include "lib/Message.h"

extern "C" {
#include <hiredis.h>
}


class ClauseSharing : public Thread {

private:
    std::string channel;
    redisContext *context_pub;
    redisContext *context_sub;

    static redisContext *Connect(const char *hostname, int port);

protected:
    void main();

public:
    ClauseSharing(char *channel, char *hostname, uint16_t port);

    ~ClauseSharing();

};


#endif //CLAUSE_SHARING_HEURISTIC_H
