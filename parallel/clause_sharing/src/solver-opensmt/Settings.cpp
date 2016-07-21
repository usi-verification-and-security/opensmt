//
// Created by Matteo Marescotti on 02/12/15.
//

#include "main.h"


Settings Settings::Default = Settings();

Settings::Settings() :
        server(Address(std::string(), 0)), clause_sharing(Address(std::string(), 0)) { }

void Settings::load(int argc, char **argv) {
    int opt;
    while ((opt = getopt(argc, argv, "hs:c:")) != -1)
        switch (opt) {
            case 'h':
                std::cout << "Usage: " << argv[0] << " [-R] [-s server-host:port][-c clause_sharing-host:port]\n";
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
                    this->clause_sharing = Address(std::string(optarg), (uint16_t) atoi(&optarg[i + 1]));
                break;
            default:
                abort();
        }
    for (int i = optind; i < argc; i++) { }
}
