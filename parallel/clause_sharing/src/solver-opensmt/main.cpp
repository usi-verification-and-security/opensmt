//
// Created by Matteo Marescotti.
//

#include "main.h"


int main(int argc, char **argv) {
    try {
        Settings::Default.load(argc, argv);
    }
    catch (Exception ex) {
        std::cerr << "Invalid argument: " << ex.what() << "\n";
    }

    if (Settings::Default.server.port > 0) {

    }


}