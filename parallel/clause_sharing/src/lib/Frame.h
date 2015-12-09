//
// Created by Matteo Marescotti on 07/12/15.
//

#ifndef CLAUSE_SHARING_SOCKET_H
#define CLAUSE_SHARING_SOCKET_H

#include <iostream>
#include <unistd.h>
#include "Exception.h"


class FrameException : public Exception {
public:
    explicit FrameException(const char *message) : Exception(message) { }

    explicit FrameException(const std::string &message) : Exception(message) { }
};


class Frame {
private:
    int fd;
    bool close;

    inline size_t readn(char *buffer, size_t length) {
        size_t r = 0;
        while (length > r) {
            ssize_t t = ::read(this->fd, &buffer[r], length - r);
            if (t == 0)
                throw FrameException("File descriptor closed");
            if (t < 0)
                throw FrameException("File descriptor error");
            r += t;
        }
        return (size_t) r;
    }

public:
    Frame(int fd) :
            fd(fd),
            close(false) { };

    Frame(int fd, bool close) :
            fd(fd),
            close(close) { };

    ~Frame() {
        std::cout << "distruct!\n";
        if (this->close)
            ::close(fd);
    }

    size_t Read(char **frame) {
        size_t length = 0;
        uint8_t buffer[4];
        if (this->readn((char *) buffer, 4) != 4)
            return 0;
        length = (size_t) buffer[0] << 24 |
                 (size_t) buffer[1] << 16 |
                 (size_t) buffer[2] << 8 |
                 (size_t) buffer[3];
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

    size_t Read(std::string &frame) {
        char *c;
        size_t lenght = this->Read(&c);
        frame.append(c, lenght);
        free(c);
        return lenght;
    }

    size_t Write(const char *frame, size_t length) {
        uint8_t buffer[4];
        buffer[3] = (uint8_t) length;
        buffer[2] = (uint8_t) (length >> 8);
        buffer[1] = (uint8_t) (length >> 16);
        buffer[0] = (uint8_t) (length >> 24);
        if (::write(this->fd, (char *) buffer, 4) != 4)
            throw FrameException("Write error");
        if ((size_t)::write(this->fd, frame, length) != length)
            throw FrameException("Write error");
        return length;
    }

    size_t Write(std::string &frame) {
        return this->Write(frame.c_str(), frame.size());
    }

    inline int FileDescriptor() {
        return this->fd;
    }

};


class Pipe {
private:
    Frame r;
    Frame w;

    Pipe(int r, int w) :
            r(Frame(r, true)),
            w(Frame(w, true)) { }

public:
    static Pipe New() {
        int fd[2];
        if (::pipe(fd) == -1)
            throw FrameException("Pipe creation error");
        return Pipe(fd[0], fd[1]);
    }

    Frame &Reader() {
        return this->r;
    }

    Frame &Writer() {
        return this->w;
    }

};


#endif //CLAUSE_SHARING_SOCKET_H
