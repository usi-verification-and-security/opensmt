//
// Created by Matteo on 12/08/16.
//

#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>
#include <algorithm>
#include <string.h>
#include "Socket.h"


Socket::Socket(Address address) {
    int sockfd;
    struct sockaddr_in server_addr;
    struct hostent *he;

    if ((sockfd = ::socket(AF_INET, SOCK_STREAM, 0)) < 0)
        throw SocketException("socket init error");

    if ((he = ::gethostbyname(address.hostname.c_str())) == nullptr)
        throw SocketException("invalid hostname");

    ::bzero(&server_addr, sizeof(server_addr));
    ::memcpy(&server_addr.sin_addr, he->h_addr_list[0], (size_t) he->h_length);
    server_addr.sin_family = AF_INET;
    server_addr.sin_port = htons(address.port);

    if (::connect(sockfd, (struct sockaddr *) &server_addr, sizeof(server_addr)) != 0)
        throw SocketException("connect error");

    new(this) Socket(sockfd);
}

Socket::Socket(uint16_t port) {
    int sockfd;
    struct sockaddr_in server_addr;

    if ((sockfd = ::socket(AF_INET, SOCK_STREAM, 0)) < 0)
        throw SocketException("socket init failed");

    int reuse = 1;
    if (setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof(int)) < 0)
        throw SocketException("socket SO_REUSEADDR failed");

    ::bzero(&server_addr, sizeof(server_addr));
    server_addr.sin_family = AF_INET;
    server_addr.sin_addr.s_addr = INADDR_ANY;
    server_addr.sin_port = htons(port);

    if (::bind(sockfd, (struct sockaddr *) &server_addr, sizeof(server_addr)) != 0)
        throw SocketException("bind failed");

    if (::listen(sockfd, 1024) != 0)
        throw SocketException("listen error");

    new(this) Socket(sockfd);
}

Socket::Socket(int fd) :
        fd(fd) {
    //std::cout << "open : " << fd << "\n";
};

Socket::~Socket() {
    //std::cout << "close: " << this->fd << "\n";
    this->close();
}

Socket *Socket::accept() {
    int clientfd;
    struct sockaddr_in client_addr;
    socklen_t addr_len = sizeof(client_addr);

    if ((clientfd = ::accept(this->fd, (struct sockaddr *) &client_addr, &addr_len)) < 0)
        throw SocketException("accept error");

    return new Socket(clientfd);
}

uint32_t Socket::readn(char *buffer, uint32_t length) {
    uint32_t r = 0;
    while (length > r) {
        ssize_t t = ::read(this->fd, &buffer[r], length - r);
        if (t == 0)
            throw SocketClosedException();
        if (t < 0)
            throw SocketException("file descriptor error");
        r += t;
    }
    return r;
}

uint32_t Socket::read(std::map<std::string, std::string> &header, std::string &payload) {
    uint32_t length = 0;
    char buffer[4];
    if (this->readn(buffer, 4) != 4)
        return 0;
    length = (uint32_t) ((uint8_t) buffer[0]) << 24 |
             (uint32_t) ((uint8_t) buffer[1]) << 16 |
             (uint32_t) ((uint8_t) buffer[2]) << 8 |
             (uint32_t) ((uint8_t) buffer[3]);
    char *message = (char *) malloc(length);
    if (message == nullptr)
        throw SocketException("can't malloc");
    try {
        length = this->readn(message, length);
    }
    catch (SocketException ex) {
        free(message);
        throw ex;
    }

    uint32_t i = 0;
    header.clear();
    while (message[i] != '\x00') {
        std::string keyval[2] = {"", ""};
        for (uint8_t j = 0; j < 2; j++) {
            uint8_t l = (uint8_t) message[i++];
            if (i + l >= length)
                throw SocketException("error during header parsing");
            keyval[j] += std::string(&message[i], l);
            i += l;
        }
        header[keyval[0]] = keyval[1];
    }
    i++;

    payload.clear();
    if (length > i)
        payload.append(std::string(&message[i], length - i));

    return length;
}

uint32_t Socket::write(const std::map<std::string, std::string> &header, const std::string &payload) {
    if (header.count(""))
        throw SocketException("empty key is not allowed");
    std::string message;
    for (auto &pair : header) {
        std::string keyval[2] = {pair.first, pair.second};
        for (uint8_t i = 0; i < 2; i++) {
            if (keyval[i].length() > (uint8_t) -1)
                throw SocketException("header key or value is too big");
            message += (char) keyval[i].length();
            message += keyval[i];
        }
    }

    message += '\x00';
    message += payload;

    if (message.length() > (uint32_t) -1)
        throw SocketException("resulting message is too big");
    uint32_t length = (uint32_t) message.length();
    char buffer[4];
    buffer[3] = (char) length;
    buffer[2] = (char) (length >> 8);
    buffer[1] = (char) (length >> 16);
    buffer[0] = (char) (length >> 24);
    if (::write(this->fd, buffer, 4) != 4)
        throw SocketException("write error");
    if (::write(this->fd, message.c_str(), length) != length)
        throw SocketException("write error");

    return length;
}

void Socket::close() {
    ::close(this->fd);
    this->fd = -1;
}

int Socket::get_fd() {
    return this->fd;
}

Address Socket::get_local() {
    struct sockaddr_storage addr;
    socklen_t addr_len = sizeof(addr);

    if (::getsockname(this->fd, (struct sockaddr *) &addr, &addr_len) < 0)
        return Address(std::string(), 0);

    return Address(&addr);
}

Address Socket::get_remote() {
    struct sockaddr_storage addr;
    socklen_t addr_len = sizeof(addr);

    if (::getpeername(this->fd, (struct sockaddr *) &addr, &addr_len) < 0)
        return Address(std::string(), 0);

    return Address(&addr);
}