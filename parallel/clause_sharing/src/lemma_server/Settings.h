//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_SETTINGS_H
#define CLAUSE_SHARING_SETTINGS_H

#include "lib/Net.h"


class Settings {
public:
    Settings();

    void load(int, char **);

    uint16_t port;
    Address server;
    std::string file_times; //TIMEDEBUG

};

#endif //CLAUSE_SHARING_SETTINGS_H
