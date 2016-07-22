//
// Created by Matteo Marescotti on 02/12/15.
//

#include <getopt.h>
#include "Settings.h"


Settings::Settings() :
        server(NULL), clause_thread(NULL) { }

Settings::~Settings() {
    delete this->server;
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
                this->server = new Socket(std::string(optarg));
                break;
            case 'c':
                this->clause_thread = new ClauseThread(Address(std::string(optarg)));
                break;
            default:
                abort();
        }
    for (int i = optind; i < argc; i++) {
        this->files.push_back(std::string(argv[i]));
    }
}
