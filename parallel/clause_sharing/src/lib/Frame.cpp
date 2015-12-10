//
// Created by Matteo Marescotti on 07/12/15.
//

#include "Frame.h"


Frame::Frame(int fd) :
        fd(fd), close(false) { };

Frame::Frame(int fd, bool close) :
        fd(fd), close(close) { };

Frame::~Frame() {
    if (this->close)
        ::close(fd);
}

uint32_t Frame::readn(char *buffer, uint32_t length) {
    uint32_t r = 0;
    while (length > r) {
        ssize_t t = ::read(this->fd, &buffer[r], length - r);
        if (t == 0)
            throw FrameException("File descriptor closed");
        if (t < 0)
            throw FrameException("File descriptor error");
        r += t;
    }
    return r;
}

uint32_t Frame::read(char **frame) {
    uint32_t length = 0;
    char buffer[4];
    if (this->readn(buffer, 4) != 4)
        return 0;
    length = (uint32_t) buffer[0] << 24 |
             (uint32_t) buffer[1] << 16 |
             (uint32_t) buffer[2] << 8 |
             (uint32_t) buffer[3];
    *frame = (char *) malloc(length);
    if (*frame == NULL)
        throw FrameException("Can't malloc");
    try {
        length = this->readn(*frame, length);
    }
    catch (char const *ex) {
        free(*frame);
        throw ex;
    }
    return length;
}

uint32_t Frame::read(std::string &frame) {
    char *c = NULL;
    uint32_t lenght = this->read(&c);
    frame.append(c, lenght);
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
        throw FrameException("Write error");
    if ((size_t) ::write(this->fd, frame, length) != length)
        throw FrameException("Write error");
    return length;
}

uint32_t Frame::write(std::string &frame) {
    return this->write(frame.c_str(), (uint32_t) frame.size());
}

int Frame::file_descriptor() {
    return this->fd;
}


Pipe::Pipe(int r, int w) :
        r(Frame(r, true)), w(Frame(w, true)) { }

Pipe Pipe::New() {
    int fd[2];
    if (::pipe(fd) == -1)
        throw FrameException("Pipe creation error");
    return Pipe(fd[0], fd[1]);
}

Frame &Pipe::reader() {
    return this->r;
}

Frame &Pipe::writer() {
    return this->w;
}
