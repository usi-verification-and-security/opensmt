//
// Created by Matteo Marescotti on 07/12/15.
//

#include "Socket.h"


Socket Socket::connect(std::string hostname, uint16_t port) {
    int sockfd;
    struct sockaddr_in serv_addr;
    struct hostent *he;

    if ((sockfd = ::socket(AF_INET, SOCK_STREAM, 0)) < 0)
        throw SocketException("socket init error");

    if ((he = ::gethostbyname(hostname.c_str())) == NULL)
        throw SocketException("invalid hostname");

    ::bzero(&serv_addr, sizeof(serv_addr));
    ::memcpy(&serv_addr.sin_addr, he->h_addr_list[0], (size_t) he->h_length);
    serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(port);

    if (::connect(sockfd, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) != 0)
        throw SocketException("connect error");

    return Socket(sockfd, true);
}

Socket::Socket(int fd) :
        fd(fd), to_be_closed(false) { };

Socket::Socket(int fd, bool to_be_closed) :
        fd(fd), to_be_closed(to_be_closed) { };

Socket::~Socket() {
    if (this->to_be_closed)
        this->close();
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
    while (message[i] != '\xFF') {
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
    std::string message;
    std::map<std::string, std::string>::iterator it;
    for (it = header.begin(); it != header.end(); it++) {
        std::string keyval[2] = {it->first, it->second};
        for (uint8_t i = 0; i < 2; i++) {
            if (keyval[i].length() > (uint8_t) -1)
                throw SocketException("header map's key or value is too big");
            message += (char) keyval[i].length();
            message += keyval[i];
        }
    }

    message += '\xFF';
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


Pipe::Pipe(int r, int w) :
        r(Socket(r, true)), w(Socket(w, true)) { }

Pipe Pipe::New() {
    int fd[2];
    if (::pipe(fd) == -1)
        throw SocketException("pipe creation error");
    return Pipe(fd[0], fd[1]);
}

Socket &Pipe::reader() {
    return this->r;
}

Socket &Pipe::writer() {
    return this->w;
}
