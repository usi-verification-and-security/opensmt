//
// Created by Matteo Marescotti on 02/12/15.
//

#include <getopt.h>
#include "lib/Log.h"
#include "Settings.h"


Settings::Settings() :
        server(NULL), clause_thread(NULL) { }

Settings::~Settings() {
    delete this->server;
    delete this->clause_thread;
}

void Settings::load_header(std::map<std::string, std::string> &header, char *string) {
    int i;
    for (i = 0; optarg[i] != '=' && optarg[i] != '\0' && i < (uint8_t) -1; i++) { }
    if (optarg[i] != '=') {
        Log::log(Log::ERROR, std::string("bad pair: ") + string);
    }
    optarg[i] = '\0';
    header[std::string(optarg)] = std::string(&optarg[i + 1]);
}


void Settings::load(int argc, char **argv) {
    int opt;
    while ((opt = getopt(argc, argv, "hs:c:r:")) != -1)
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
            case 'r':
                this->load_header(this->header_solve, optarg);
                break;
            default:
                abort();
        }
    for (int i = optind; i < argc; i++) {
        this->files.push_back(std::string(argv[i]));
    }
}