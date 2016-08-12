//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_SETTINGS_H
#define CLAUSE_SHARING_SETTINGS_H

#include "lib/net.h"


class Settings {
public:
    Settings();

    void load(int, char **);

    uint16_t port;
    Address server;

};

#endif //CLAUSE_SHARING_SETTINGS_H
