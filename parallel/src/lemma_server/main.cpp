#include <iostream>
#include "lib/Log.h"
#include "Settings.h"
#include "LemmaServer.h"


int main(int argc, char **argv) {
    Settings settings = Settings();
    try {
        settings.load(argc, argv);
    }
    catch (Exception &ex) {
        Log::log(Log::ERROR, ex.what());
    }

    try {
        LemmaServer server(settings);
        server.run_forever();
    } catch (SQLiteException &ex) {
        Log::log(Log::ERROR, ex.what());
    } catch (SocketException &ex) {
        Log::log(Log::ERROR, ex.what());
    } catch (Exception &ex) {
        Log::log(Log::INFO, ex.what());
    }
}