//
// Created by Matteo on 12/08/16.
//

#include <unistd.h>
#include <algorithm>
#include "Server.h"


Server::Server(Socket *socket, bool close) :
        socket(socket) {
    if (this->socket)
        this->sockets[this->socket] = close;
}

Server::Server() : Server(nullptr, false) { }

Server::Server(Socket &socket) :
        Server(&socket, false) { }

Server::Server(uint16_t port) :
        Server(new Socket(port), true) { }

Server::~Server() {
    for (auto &pair:this->sockets) {
        if (pair.second)
            delete pair.first;
    }
}

void Server::run_forever() {
    fd_set readset;
    int result;
    Socket *client;
    std::map<std::string, std::string> header;
    std::string payload;

    while (true) {
        do {
            FD_ZERO(&readset);
            int max = 0;
            for (auto &pair : this->sockets) {
                if (pair.first->get_fd() < 0)
                    continue;
                max = max < pair.first->get_fd() ? pair.first->get_fd() : max;
                FD_SET(pair.first->get_fd(), &readset);
            }
            if (max == 0)
                return;
            result = ::select(max + 1, &readset, nullptr, nullptr, nullptr);
        } while (result == -1 && errno == EINTR);

        auto pair = this->sockets.begin();
        while (pair != this->sockets.end()) {
            if (FD_ISSET(pair->first->get_fd(), &readset)) {
                FD_CLR(pair->first->get_fd(), &readset);
                if (this->socket && pair->first->get_fd() == this->socket->get_fd()) {
                    try {
                        client = this->socket->accept();
                    }
                    catch (SocketException ex) {
                        pair++;
                        continue;
                    }
                    this->sockets[client] = true;
                    this->handle_accept(*client);
                }
                else {
                    try {
                        pair->first->read(header, payload);
                        this->handle_message(*pair->first, header, payload);
                    }
                    catch (SocketClosedException ex) {
                        this->handle_close(*pair->first);
                        pair->first->close();
                        this->del_socket(pair++->first);
                        continue;
                    }
                    catch (SocketException ex) {
                        this->handle_exception(*pair->first, ex);
                    }
                }
            }
            ++pair;
        }
//        if (result < 0) {
//        }
    }
}

void Server::add_socket(Socket *socket) {
    if (this->sockets.count(socket) == 0)
        this->sockets[socket] = false;
}

void Server::del_socket(Socket *socket) {
    auto it = this->sockets.find(socket);
    if (it == this->sockets.end())
        return;
    if (it->second)
        delete socket;
    this->sockets.erase(it);
}