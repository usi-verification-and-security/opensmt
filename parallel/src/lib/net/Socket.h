//
// Created by Matteo on 12/08/16.
//

#ifndef CLAUSE_SERVER_SOCKET_H
#define CLAUSE_SERVER_SOCKET_H

#include <map>
#include "lib/Exception.h"
#include "Address.h"


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

    inline uint32_t readn(char *, uint32_t);

public:
    Socket(int);

    Socket(Address);

    Socket(uint16_t);

    ~Socket();

    Socket *accept();

    uint32_t read(std::map<std::string, std::string> &, std::string &);

    uint32_t write(const std::map<std::string, std::string> &, const std::string &);

    void close();

    int get_fd();

    Address get_local();

    Address get_remote();

};


#endif //CLAUSE_SERVER_SOCKET_H
