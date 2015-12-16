//
// Created by Matteo Marescotti on 07/12/15.
//

#include "Frame.h"


Frame Frame::connect(std::string hostname, uint16_t port) {
    int sockfd;
    struct sockaddr_in serv_addr;
    struct hostent *he;

    if ((sockfd = ::socket(AF_INET, SOCK_STREAM, 0)) < 0)
        throw FrameException("socket init error");

    if ((he = ::gethostbyname(hostname.c_str())) == NULL)
        throw FrameException("invalid hostname");

    ::bzero(&serv_addr, sizeof(serv_addr));
    ::memcpy(&serv_addr.sin_addr, he->h_addr_list[0], (size_t) he->h_length);
    serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(port);

    if (::connect(sockfd, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) != 0)
        throw FrameException("connect error");

    return Frame(sockfd, true);
}

Frame::Frame(int fd) :
        fd(fd), to_be_closed(false) { };

Frame::Frame(int fd, bool to_be_closed) :
        fd(fd), to_be_closed(to_be_closed) { };

Frame::~Frame() {
    this->close();
}

uint32_t Frame::readn(char *buffer, uint32_t length) {
    uint32_t r = 0;
    while (length > r) {
        ssize_t t = ::read(this->fd, &buffer[r], length - r);
        if (t == 0)
            throw FrameException("file descriptor closed");
        if (t < 0)
            throw FrameException("file descriptor error");
        r += t;
    }
    return r;
}

uint32_t Frame::read(char **frame) {
    uint32_t length = 0;
    uint8_t buffer[4];
    if (this->readn((char *) buffer, 4) != 4)
        return 0;
    length = (uint32_t) buffer[0] << 24 | (uint32_t) buffer[1] << 16 | (uint32_t) buffer[2] << 8 | (uint32_t) buffer[3];
    *frame = (char *) malloc(length);
    if (*frame == NULL)
        throw FrameException("can't malloc");
    try {
        length = this->readn(*frame, length);
    }
    catch (FrameException ex) {
        free(*frame);
        throw ex;
    }
    return length;
}

uint32_t Frame::read(std::string &frame) {
    char *c = NULL;
    uint32_t lenght = this->read(&c);
    frame = std::string(c, lenght);
    free(c);
    return lenght;
}

uint32_t Frame::write(const char *frame, uint32_t length) {
    char buffer[4];
    buffer[3] = (char) length;
    buffer[2] = (char) (length >> 8);
    buffer[1] = (char) (length >> 16);
    buffer[0] = (char) (length >> 24);
    if (::write(this->fd, buffer, 4) != 4)
        throw FrameException("write error");
    if ((size_t) ::write(this->fd, frame, length) != length)
        throw FrameException("write error");
    return length;
}

uint32_t Frame::write(std::string &frame) {
    return this->write(frame.c_str(), (uint32_t) frame.size());
}

void Frame::close() {
    if (!this->to_be_closed)
        return;
    ::close(this->fd);
    this->to_be_closed = false;
    this->fd = -1;
}

int Frame::file_descriptor() {
    return this->fd;
}


Pipe::Pipe(int r, int w) :
        r(Frame(r, true)), w(Frame(w, true)) { }

Pipe Pipe::New() {
    int fd[2];
    if (::pipe(fd) == -1)
        throw FrameException("pipe creation error");
    return Pipe(fd[0], fd[1]);
}

Frame &Pipe::reader() {
    return this->r;
}

Frame &Pipe::writer() {
    return this->w;
}
