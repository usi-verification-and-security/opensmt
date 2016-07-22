//
// Created by Matteo Marescotti on 02/12/15.
//

#include "Settings.h"
#include <getopt.h>

Settings::Settings() :
        server(Address(std::string(), 0)), clause_thread(NULL) { }

Settings::~Settings() {
    delete this->clause_thread;
}

void Settings::load(int argc, char **argv) {
    int opt;
    while ((opt = getopt(argc, argv, "hs:c:")) != -1)
        switch (opt) {
            case 'h':
                std::cout << "Usage: " << argv[0] << " [-R] [-s server-host:port][-c clause_server-host:port]\n";
                exit(0);
            case 's':
            case 'c':
                uint8_t i;
                for (i = 0; optarg[i] != ':' && optarg[i] != '\0' && i < (uint8_t) -1; i++) { }
                if (optarg[i] != ':')
                    throw Exception("invalid host:port");
                optarg[i] = '\0';
                if (opt == 's')
                    this->server = Address(std::string(optarg), (uint16_t) atoi(&optarg[i + 1]));
                else if (opt == 'c')
                    this->clause_thread = new ClauseThread(
                            Address(std::string(optarg), (uint16_t) atoi(&optarg[i + 1])));
                //Address(std::string(optarg), (uint16_t) atoi(&optarg[i + 1]));
                break;
            default:
                abort();
        }
    for (int i = optind; i < argc; i++) {
        this->files.push_back(std::string(argv[i]));
    }
}
