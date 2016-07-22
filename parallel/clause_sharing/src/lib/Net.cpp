//
// Created by Matteo Marescotti on 07/12/15.
//

#include "Net.h"
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>


Address::Address(std::string address) {
    uint8_t i;
    for (i = 0; address[i] != ':' && i < address.size() && i < (uint8_t) -1; i++) { }
    if (address[i] != ':')
        throw Exception("invalid host:port");
    new(this) Address(address.substr(0, i), (uint16_t) ::atoi(address.substr(i + 1).c_str()));
}

Address::Address(std::string hostname, uint16_t port) :
        hostname(hostname),
        port(port) { }

Address::Address(struct sockaddr_storage *address) {
    char ipstr[INET6_ADDRSTRLEN];
    uint16_t port = 0;

    if (address->ss_family == AF_INET) {
        struct sockaddr_in *s = (struct sockaddr_in *) address;
        port = ntohs(s->sin_port);
        ::inet_ntop(AF_INET, &s->sin_addr, ipstr, sizeof ipstr);
    } else { // AF_INET6
        struct sockaddr_in6 *s = (struct sockaddr_in6 *) address;
        port = ntohs(s->sin6_port);
        ::inet_ntop(AF_INET6, &s->sin6_addr, ipstr, sizeof ipstr);
    }

    new(this) Address(std::string(ipstr), port);
}


Socket::Socket(Address address) {
    int sockfd;
    struct sockaddr_in server_addr;
    struct hostent *he;

    if ((sockfd = ::socket(AF_INET, SOCK_STREAM, 0)) < 0)
        throw SocketException("socket init error");

    if ((he = ::gethostbyname(address.hostname.c_str())) == NULL)
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
    length = (uint32_t) buffer[0] << 24 | (uint32_t) buffer[1] << 16 | (uint32_t) buffer[2] << 8 | (uint32_t) buffer[3];
    char *message = (char *) malloc(length);
    if (message == NULL)
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

uint32_t Socket::write(std::map<std::string, std::string> &header, std::string &payload) {
    if (header.count(""))
        throw SocketException("empty key is not allowed");
    std::string message;
    for (auto pair = header.begin(); pair != header.end(); ++pair) {
        std::string keyval[2] = {pair->first, pair->second};
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
        throw SocketException("getsockname error");

    return Address(&addr);
}

Address Socket::get_remote() {
    struct sockaddr_storage addr;
    socklen_t addr_len = sizeof(addr);

    if (::getpeername(this->fd, (struct sockaddr *) &addr, &addr_len) < 0)
        throw SocketException("getpeername error");

    return Address(&addr);
}

Pipe::Pipe(int r, int w) :
        r(new Socket(r)),
        w(new Socket(w)) { }

Pipe::Pipe() {
    int fd[2];
    if (::pipe(fd) == -1)
        throw SocketException("pipe creation error");
    new(this) Pipe(fd[0], fd[1]);
}

Pipe::~Pipe() {
    delete this->r;
    delete this->w;
}

Socket *Pipe::reader() {
    return this->r;
}

Socket *Pipe::writer() {
    return this->w;
}

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
            for (auto socket = this->sockets.begin(); socket != this->sockets.end(); ++socket) {
                max = max < (*socket)->get_fd() ? (*socket)->get_fd() : max;
                FD_SET((*socket)->get_fd(), &readset);
            }
            if (max == 0)
                return;
            result = select(max + 1, &readset, NULL, NULL, NULL);
        } while (result == -1 && errno == EINTR);

        while (result > 0) {
            for (auto socket = this->sockets.begin(); socket != this->sockets.end(); ++socket) {
                if (FD_ISSET((*socket)->get_fd(), &readset)) {
                    FD_CLR((*socket)->get_fd(), &readset);
                    result--;
                    if (this->socket && (*socket)->get_fd() == this->socket->get_fd()) {
                        client = this->socket->accept();
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
                            this->sockets.erase(socket);
                        }
                        catch (SocketException ex) {
                            this->handle_exception(**socket, ex);
                        }
                    }
                    break;
                }
            }

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