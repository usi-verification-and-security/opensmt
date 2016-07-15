//
// Created by Matteo Marescotti on 07/12/15.
//

#ifndef CLAUSE_SHARING_SOCKET_H
#define CLAUSE_SHARING_SOCKET_H

#include <iostream>
#include <map>
#include <unistd.h>
#include <string.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netdb.h>
#include "Exception.h"


class SocketException : public Exception {
public:
    explicit SocketException(const char *message) : SocketException(std::string(message)) { }

    explicit SocketException(const std::string &message) : Exception("SocketException: " + message) { }
};


class SocketClosedException : public SocketException {
public:
    explicit SocketClosedException() : SocketException("file descriptor closed") { }
};


class Socket {
private:
    int fd;
    bool to_be_closed;

    inline uint32_t readn(char *buffer, uint32_t length);

public:
    static Socket connect(std::string hostname, uint16_t port);

    Socket(int fd);

    Socket(int fd, bool to_be_closed);

    ~Socket();

    uint32_t read(std::map<std::string, std::string> &header, std::string &payload);

    uint32_t write(std::map<std::string, std::string> &header, std::string &payload);

    void close();

    int get_fd();

};


class Pipe {
private:
    Socket r;
    Socket w;

    Pipe(int r, int w);

public:
    static Pipe New();

    Socket &reader();

    Socket &writer();

};


#endif //CLAUSE_SHARING_SOCKET_H
