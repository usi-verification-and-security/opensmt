//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_HEURISTIC_H
#define CLAUSE_SHARING_HEURISTIC_H

#include <iostream>
#include "Sort.h"
#include "lib/Process.h"
#include "lib/Message.h"

extern "C" {
#include <hiredis.h>
}


class Settings {
public:
    typedef struct {
        std::string hostname;
        uint16_t port;
    } Address;

    static Settings Default;

    Settings() :
            redis({.hostname=std::string("127.0.0.1"), .port=6379}) { }

    void load(int argc, char **argv);

    Address redis;
    std::string channel;

};


class ClauseSharing : public Thread {

private:
    std::string channel;
    redisContext *context_pub;
    redisContext *context_sub;

    static redisContext *Connect(std::string &hostname, int port);

protected:
    void main();

public:
    ClauseSharing(std::string &channel, std::string &hostname, uint16_t port);

    ~ClauseSharing();

};


#endif //CLAUSE_SHARING_HEURISTIC_H

