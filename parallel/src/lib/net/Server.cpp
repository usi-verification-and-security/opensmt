//
// Created by Matteo on 12/08/16.
//

#include <unistd.h>
#include <algorithm>
#include "Server.h"


Server::Server(Socket *socket, bool close) :
        socket(socket),
        close(close) {
    if (this->socket)
        this->sockets.push_back(this->socket);
}

Server::Server() : Server(NULL, false) { }

Server::Server(Socket &socket) :
        Server(&socket, false) { }

Server::Server(uint16_t port) :
        Server(new Socket(port), true) { }

Server::~Server() {
    for (auto socket:this->sockets) {
        socket->close();
    }
    if (this->close)
        delete this->socket;
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
            for (auto socket : this->sockets) {
                if (socket->get_fd() < 0)
                    continue;
                max = max < socket->get_fd() ? socket->get_fd() : max;
                FD_SET(socket->get_fd(), &readset);
            }
            if (max == 0)
                return;
            result = ::select(max + 1, &readset, NULL, NULL, NULL);
        } while (result == -1 && errno == EINTR);

        for (auto socket = this->sockets.begin(); socket != this->sockets.end();) {
            if (FD_ISSET((*socket)->get_fd(), &readset)) {
                FD_CLR((*socket)->get_fd(), &readset);
                if (this->socket && (*socket)->get_fd() == this->socket->get_fd()) {
                    try {
                        client = this->socket->accept();
                    }
                    catch (SocketException ex) {
                        goto next;
                    }
                    this->sockets.push_back(client);
                    this->handle_accept(*client);
                }
                else {
                    try {
                        (*socket)->read(header, payload);
                        this->handle_message(**socket, header, payload);
                    }
                    catch (SocketClosedException ex) {
                        this->handle_close(**socket);
                        (*socket)->close();
                        socket = this->sockets.erase(socket);
                    }
                    catch (SocketException ex) {
                        this->handle_exception(**socket, ex);
                    }
                }
            }
            next:
            ++socket;
        }
//        if (result < 0) {
//        }
    }
}

void Server::add_socket(Socket *socket) {
    this->sockets.push_back(socket);
}

void Server::del_socket(Socket *socket) {
    this->sockets.erase(
            std::remove_if(
                    this->sockets.begin(),
                    this->sockets.end(),
                    [&](Socket *it) {
                        return it == socket;
                    }
            ),
            this->sockets.end());
}