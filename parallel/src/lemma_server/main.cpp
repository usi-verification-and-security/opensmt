#include <iostream>
#include "Settings.h"
#include "LemmaServer.h"
#include "ServerThread.h"


int main(int argc, char **argv) {
    Settings settings = Settings();
    try {
        settings.load(argc, argv);
    }
    catch (Exception ex) {
        std::cerr << ex.what() << "\n";
    }

    ServerThread *st = NULL;
    if (settings.server.port > 0) {
        st = new ServerThread(settings);
    }

    LemmaServer server(settings);
    server.run_forever();

    delete (st);
}