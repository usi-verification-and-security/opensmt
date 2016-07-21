//
// Created by Matteo Marescotti on 02/12/15.
//

#include <getopt.h>
#include "Settings.h"


Settings::Settings() :
        port(5000), server(Address(std::string(), 0)) { }

void Settings::load(int argc, char **argv) {
    int opt;
    while ((opt = getopt(argc, argv, "hp:s:")) != -1)
        switch (opt) {
            case 'h':
                std::cout << "Usage: " << argv[0] << "\n";
                exit(0);
            case 'p':
                this->port = (uint16_t) atoi(optarg);
                break;
            case 's':
                uint8_t i;
                for (i = 0; optarg[i] != ':' && optarg[i] != '\0' && i < (uint8_t) -1; i++) { }
                if (optarg[i] != ':')
                    throw Exception("invalid host:port");
                optarg[i] = '\0';
                this->server = Address(std::string(optarg), (uint16_t) atoi(&optarg[i + 1]));
                break;
            default:
                abort();
        }

    for (int i = optind; i < argc; i++) { }
}
