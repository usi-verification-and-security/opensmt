//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_SETTINGS_H
#define CLAUSE_SHARING_SETTINGS_H

#include "main.h"


Settings Settings::Default = Settings();

void Settings::load(int argc, char **argv) {
    int opt;
    while ((opt = getopt(argc, argv, "c:r:")) != -1)
        switch (opt) {
            case 'r':
                uint8_t i;
                for (i = 0; optarg[i] != ':' && optarg[i] != '\0' && i < (uint8_t) - 1; i++) { }
                if (optarg[i] != ':')
                    throw "Invalid host:port argument\n";
                optarg[i] = '\0';
                this->redis = {.hostname=std::string(optarg), .port=(uint16_t) atoi(&optarg[i + 1])};
                break;
            case 'c':
                this->channel = std::string(optarg);
                break;
            default:
                abort();
        }
}


#endif //CLAUSE_SHARING_HEURISTIC_H
