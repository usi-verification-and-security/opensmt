//
// Created by Matteo on 12/08/16.
//

#ifndef CLAUSE_SERVER_ADDRESS_H
#define CLAUSE_SERVER_ADDRESS_H

#include <string>


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


#endif //CLAUSE_SERVER_ADDRESS_H
