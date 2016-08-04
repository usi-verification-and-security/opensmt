//
// Created by Matteo on 20/07/16.
//

#include <unistd.h>
#include <lib/Log.h>
#include "ClauseThread.h"


ClauseThread::ClauseThread(Address address) :
        Thread(), address(address), socket(NULL) {
    this->start();
}

ClauseThread::~ClauseThread() {
    delete this->socket;
}

void ClauseThread::log(uint8_t level, std::string message) {
    Log::log(level, "ClauseThread: " + message);
}

void ClauseThread::main() {
    const uint8_t retry = 5;
    while (true) {
        try {
            std::map<std::string, std::string> header;
            std::string payload;
            this->socket = new Socket(this->address);
            this->log(Log::INFO, "connected to " + this->address.toString());
            while (true) {
                this->reader()->read(header, payload);
                //Log::log(Log::INFO, "ricevo: " + payload);
                this->socket->write(header, payload);
            }
        }
        catch (...) {
            this->log(Log::WARNING, "server closed connection, retry in " + std::to_string(retry) + " seconds");
        }
        ::sleep(retry);
    }
}
