//
// Created by Matteo on 19/07/16.
//

#include "main.h"

ServerThread::ServerThread(Settings &settings) :
        Thread(), settings(settings), server(NULL) {
    this->start();
}

ServerThread::~ServerThread() {
    delete (this->server);
}

void ServerThread::main() {
    try {
        this->server = new Socket(settings.server);
        std::map<std::string, std::string> header;
        std::string payload;
        header["clauses"] = ":" + std::to_string(settings.port);
        this->server->write(header, payload);
        while (true) {
            this->server->read(header, payload);
            if (header["command"] == "exit") {
                exit(0);
            }
        }
    }
    catch (SocketException) {
        Log::log(Log::ERROR, "server connection error");
    }
}


