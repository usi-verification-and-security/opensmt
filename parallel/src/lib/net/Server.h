//
// Created by Matteo on 12/08/16.
//

#ifndef CLAUSE_SERVER_SERVER_H
#define CLAUSE_SERVER_SERVER_H

#include <list>
#include <map>
#include "Socket.h"


class Server {
private:
    Socket *socket;
    std::map<Socket *, bool> sockets;


    Server(Socket *, bool);

protected:
    virtual void handle_accept(Socket &) { }

    virtual void handle_close(Socket &) { }

    virtual void handle_message(Socket &, std::map<std::string, std::string> &, std::string &) { }

    virtual void handle_exception(Socket &, SocketException &) { }

public:
    Server();

    Server(Socket &);

    Server(uint16_t);

    virtual ~Server();

    void run_forever();

    void add_socket(Socket *);

    void del_socket(Socket *);

};


#endif //CLAUSE_SERVER_SERVER_H
