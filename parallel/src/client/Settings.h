//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_SETTINGS_H
#define CLAUSE_SHARING_SETTINGS_H

#include <list>
#include "lib/net.h"


class Settings {
private:
    void load_header(std::map<std::string, std::string> &header, char *string);

public:
    Settings();

    ~Settings();

    void load(int, char **);

    Address *server;
    Address *lemmas;
    std::list<std::string> files;
    std::map<std::string, std::string> header_solve;
};

#endif //CLAUSE_SHARING_SETTINGS_H
