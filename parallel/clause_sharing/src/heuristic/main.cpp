#include "main.h"


int main(int argc, char **argv) {
    try {
        Settings::Default.load(argc, argv);
    }
    catch (Exception ex) {
        std::cerr << ex.what() << "\n";
    }

    ServerThread *st = NULL;

    if (Settings::Default.server.port > 0) {
        st = new ServerThread(Settings::Default);
    }

    HeuriscticServer server(Settings::Default.port);

    server.run_forever();

    delete (st);
}