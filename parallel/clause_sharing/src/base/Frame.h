//
// Created by Matteo Marescotti on 07/12/15.
//

#ifndef CLAUSE_SHARING_SOCKET_H
#define CLAUSE_SHARING_SOCKET_H

#include <iostream>
#include <unistd.h>
#include <tuple>


class Frame {
private:
    int fd;
    bool close;

    inline uint32_t readn(char *buffer, uint32_t length) {
        uint32_t r = 0;
        while (length > r) {
            r += (uint32_t) ::read(this->fd, &buffer[r], length - r);
            if (r == 0)
                throw "Server connection broken";
        }
        return r;
    }

public:
    static std::tuple<Frame, Frame> Pipe() {
        int fd[2];
        if (::pipe(fd) == -1)
            throw "Pipe creation error";
        return std::make_tuple(Frame(fd[0]), Frame(fd[1]));
    }

    Frame(int fd) :
            fd(fd),
            close(false) { };

    Frame(int fd, bool close) :
            fd(fd),
            close(close) { };

    ~Frame() {
        if (this->close)
            ::close(fd);
    }

    uint32_t Read(char **frame) {
        uint32_t length = 0;
        uint8_t buffer[4];
        if (this->readn((char *) buffer, 4) != 4)
            return 0;
        length = (uint32_t) buffer[0] << 24 |
                 (uint32_t) buffer[1] << 16 |
                 (uint32_t) buffer[2] << 8 |
                 (uint32_t) buffer[3];
        *frame = (char *) malloc(length);
        if (*frame == NULL)
            throw "Can't malloc";
        try {
            length = this->readn(*frame, length);
        }
        catch (char const *ex) {
            free(*frame);
            throw ex;
        }
        return length;
    }

    uint32_t Write(char *frame, uint32_t length) {
        uint8_t buffer[4];
        buffer[3] = (uint8_t) length;
        buffer[2] = (uint8_t) (length >> 8);
        buffer[1] = (uint8_t) (length >> 16);
        buffer[0] = (uint8_t) (length >> 24);
        if (::write(this->fd, (char *) buffer, 4) != 4)
            return 0;
        return (uint32_t) ::write(this->fd, frame, length);
    }

    inline int FileDescriptor() {
        return this->fd;
    }

};


#endif //CLAUSE_SHARING_SOCKET_H
