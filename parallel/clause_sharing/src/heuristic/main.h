//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef HEURISTIC_H
#define HEURISTIC_H

#include <iostream>
#include <vector>
#include "Sort.h"
#include "lib/Net.h"
#include "lib/Thread.h"
#include "lib/Log.h"


class Settings {
public:
    static Settings Default;

    Settings();

    void load(int, char **);

    uint16_t port;
    Address server;

};


// thread to handle the connection with the server
class ServerThread : public Thread {
private:
    Settings &settings;
    Socket *server;

protected:
    void main();

public:
    ServerThread(Settings &);

    ~ServerThread();

};


class HeuriscticServer : public Server {
public:
    HeuriscticServer(uint16_t port) : Server(port) { }

protected:
    void handle_accept(Socket &);

    void handle_close(Socket &);

    void handle_message(Socket &, std::map<std::string, std::string> &, std::string &);

    void handle_exception(Socket &, SocketException &);
};

#endif //HEURISTIC_H

