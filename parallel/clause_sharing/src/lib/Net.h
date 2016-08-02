//
// Created by Matteo Marescotti on 07/12/15.
//

#ifndef CLAUSE_SHARING_SOCKET_H
#define CLAUSE_SHARING_SOCKET_H

#include <iostream>
#include <map>
#include <list>
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


class Address {
public:
    Address(std::string);

    Address(std::string, uint16_t);

    Address(struct sockaddr_storage *);

    std::string toString() {
        return this->hostname + ":" + std::to_string(this->port);
    }

    std::string hostname;
    uint16_t port;
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

    uint32_t write(std::map<std::string, std::string> &, std::string &);

    void close();

    int get_fd();

    Address get_local();

    Address get_remote();

};


class Pipe {
private:
    Socket *r;
    Socket *w;

    Pipe(int, int);

public:
    Pipe();

    ~Pipe();

    Socket *reader();

    Socket *writer();

};


class Server {
private:
    Socket *socket;
    std::list<Socket *> sockets;
    bool close;


    Server(Socket *, bool);

public:
    Server();

    Server(Socket &);

    Server(uint16_t);

    ~Server();

    void run_forever();

    void add_socket(Socket *);

    void del_socket(Socket *);

protected:
    virtual void handle_accept(Socket &) { }

    virtual void handle_close(Socket &) { }

    virtual void handle_message(Socket &, std::map<std::string, std::string> &, std::string &) { }

    virtual void handle_exception(Socket &, SocketException &) { }
};


#endif //CLAUSE_SHARING_SOCKET_H
