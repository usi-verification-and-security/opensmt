//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_SETTINGS_H
#define CLAUSE_SHARING_SETTINGS_H

#include "main.h"


Settings Settings::Default = Settings();

void Settings::load(int argc, char **argv) {
    int opt;
    while ((opt = getopt(argc, argv, "hRr:s:")) != -1)
        switch (opt) {
            case 'h':
                std::cout << "Usage: " << argv[0] << " [-R] [-r redis-host:port] [-s server-host:port]\n";
                exit(0);
            case 'R':
                this->clause_sharing = false;
                break;
            case 'r':
            case 's':
                uint8_t i;
                for (i = 0; optarg[i] != ':' && optarg[i] != '\0' && i < (uint8_t) -1; i++) { }
                if (optarg[i] != ':')
                    throw Exception("invalid host:port argument");
                optarg[i] = '\0';
                if (opt == 's')
                    this->server = {.hostname=std::string(optarg), .port=(uint16_t) atoi(&optarg[i + 1])};
                else if (opt == 'r')
                    this->redis = {.hostname=std::string(optarg), .port=(uint16_t) atoi(&optarg[i + 1])};
                break;
            default:
                abort();
        }
}


#endif //CLAUSE_SHARING_HEURISTIC_H
