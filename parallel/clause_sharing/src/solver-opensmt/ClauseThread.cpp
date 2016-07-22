//
// Created by Matteo on 20/07/16.
//

#include <lib/Log.h>
#include "main.h"


ClauseThread::ClauseThread(Address address) :
        Thread(), address(address), socket(NULL) {
    this->start();
}

ClauseThread::~ClauseThread() {
    delete this->socket;
}

void ClauseThread::main() {
    const uint8_t retry = 5;
    while (true) {
        try {
            std::map<std::string, std::string> header;
            std::string payload;
            this->socket = new Socket(this->address);
            Log::log(Log::INFO, "clause sharing connected to " + this->address.toString());
            while (true) {
                this->reader()->read(header, payload);
                //Log::log(Log::INFO, "ricevo: " + payload);
                this->socket->write(header, payload);
            }
        }
        catch (...) {
            Log::log(Log::WARNING, "clause sharing connection closed, retry in " + std::to_string(retry) + " seconds");
        }
        ::sleep(retry);
    }
}


