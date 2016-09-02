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
        std::cerr << "argument parsing error: " << ex.what() << "\n";
        exit(1);
    }

    FileThread *ft = nullptr;
    if (settings.server == nullptr && settings.files.size() > 0) {
        ft = new FileThread(settings);
    }

    if (settings.server != nullptr) {
        try {
            SolverServer ss(*settings.server);
            ss.run_forever();
        } catch (SocketException &ex) {
            Log::log(Log::ERROR, ex.what());
        }
    }
    delete ft;
    Log::log(Log::INFO, "all done. bye!");
}