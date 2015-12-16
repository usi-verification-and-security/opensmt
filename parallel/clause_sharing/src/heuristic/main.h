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

};


class Heuristic : public Thread {

private:
    redisContext *context_pub;
    redisContext *context_sub;

    static redisContext *Connect(std::string &hostname, uint16_t port);

protected:
    void main();

public:
    Heuristic(std::string &hostname, uint16_t port);

    ~Heuristic();

};


#endif //CLAUSE_SHARING_HEURISTIC_H

