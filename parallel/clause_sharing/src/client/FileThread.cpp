//
// Created by Matteo on 22/07/16.
//

#include <iostream>
#include <fstream>
#include "lib/Log.h"
#include "FileThread.h"


FileThread::FileThread(Settings &settings) : settings(settings), client(NULL) {
    if (settings.server != NULL)
        throw Exception("server must be null");
    Socket server((uint16_t) 0);
    this->client = new Socket(Address(server.get_local().toString()));
    settings.server = server.accept();
    this->start();
}

FileThread::~FileThread() {
    delete this->client;
}

void FileThread::main() {
    uint32_t n = 0;
    for (auto filename : this->settings.files) {
        std::ifstream file(filename);
        if (!file.is_open()) {
            Log::log(Log::WARNING, "unable to open: " + filename);
            continue;
        }

        std::string content;
        file.seekg(0, std::ios::end);
        content.resize((unsigned long) file.tellg());
        file.seekg(0, std::ios::beg);
        file.read(&content[0], content.size());
        file.close();

        std::map<std::string, std::string> header;
        header["command"] = "solve";
        header["name"] = filename;
        header["hash"] = std::to_string(n++);
        this->client->write(header, content);
        this->client->read(header, content);
        header["command"] = "stop";
        this->client->write(header, content);
    }

    this->client->close();

}