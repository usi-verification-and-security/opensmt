//
// Created by Matteo Marescotti.
//

#include <iostream>
#include "lib/Log.h"
#include "Settings.h"
#include "SolverServer.h"
#include "FileThread.h"


int main(int argc, char **argv) {
    Settings settings;
    try {
        settings.load(argc, argv);
    }
    catch (Exception ex) {
        std::cerr << "Invalid argument: " << ex.what() << "\n";
    }

    FileThread *ft = NULL;
    if (settings.server == NULL && settings.files.size() > 0) {
        ft = new FileThread(settings);
    }

    if (settings.server != NULL) {
        SolverServer ss(settings, *settings.server);
        ss.run_forever();
    }

    delete ft;

    Log::log(Log::INFO, "all done. bye!");
}