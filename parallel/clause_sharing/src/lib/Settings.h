//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_SETTINGS_H
#define CLAUSE_SHARING_SETTINGS_H

#include <iostream>


class Settings {
public:
    static Settings Default;

    static Settings &Load(int argc, char **argv);

    Settings();

    std::string redis_hostname;
    uint16_t redis_port;

};


#endif //CLAUSE_SHARING_HEURISTIC_H
