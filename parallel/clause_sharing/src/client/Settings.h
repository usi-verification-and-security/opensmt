//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_SETTINGS_H
#define CLAUSE_SHARING_SETTINGS_H

#include <list>
#include "lib/Net.h"
#include "ClauseThread.h"


class Settings {
private:
    void load_header(std::map<std::string, std::string> &header, char *string);
    ClauseThread *clause_thread;
public:
    Settings();

    ~Settings();

    void load(int, char **);

    Socket *get_clause_agent() { return this->clause_thread ? this->clause_thread->writer() : NULL; }

    Socket *server;
    std::list<std::string> files;
    std::map<std::string, std::string> header_solve;
};

#endif //CLAUSE_SHARING_SETTINGS_H
