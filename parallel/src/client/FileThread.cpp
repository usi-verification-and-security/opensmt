//
// Created by Matteo on 22/07/16.
//

#include <iostream>
#include <fstream>
#include "lib/Log.h"
#include "FileThread.h"


FileThread::FileThread(Settings &settings) : settings(settings), server(nullptr) {
    if (settings.server != nullptr)
        throw Exception("server must be null");
    this->server = new Socket((uint16_t) 0);
    settings.server = new Address(this->server->get_local());
    this->start();
}

FileThread::~FileThread() {
    delete this->server;
}

void FileThread::main() {
    std::map<std::string, std::string> header;

    Socket client = *this->server->accept();
    Socket *lemmas = nullptr;

    if (this->settings.lemmas != nullptr) {
        try {
            lemmas = new Socket(*this->settings.lemmas);
        } catch (SocketException) { }
        header["command"] = "lemmas";
        header["lemmas"] = this->settings.lemmas->toString();
        client.write(header, "");
    }

    for (auto &filename : this->settings.files) {
        std::ifstream file(filename);
        if (!file.is_open()) {
            Log::log(Log::WARNING, "unable to open: " + filename);
            continue;
        }

        std::string payload;
        file.seekg(0, std::ios::end);
        payload.resize((unsigned long) file.tellg());
        file.seekg(0, std::ios::beg);
        file.read(&payload[0], payload.size());
        file.close();

        header.clear();
        for (auto &it : this->settings.header_solve)
            header[it.first] = it.second;
        header["command"] = "solve";
        header["name"] = filename;
        header["node"] = "[]";
        client.write(header, payload);
        do {
            client.read(header, payload);
//            for (auto p:header) {
//                std::cout << p.first << " " << p.second << "\n";
//            }
//            std::cout << "\n";
        } while (header.count("status") == 0);
        if (lemmas != nullptr)
            try {
                header["lemmas"] = std::string("0");
                lemmas->write(header, "");
            } catch (SocketException) {
                delete lemmas;
                lemmas = nullptr;
            }
        header["command"] = "stop";
        client.write(header, "");
    }
    delete lemmas;
}