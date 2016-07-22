#include "main.h"


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

    ClauseServer server(settings.port);
    server.run_forever();

    delete (st);
}