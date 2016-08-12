//
// Created by Matteo on 12/08/16.
//

#ifndef CLAUSE_SERVER_PIPE_H
#define CLAUSE_SERVER_PIPE_H

#include "Socket.h"


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


#endif //CLAUSE_SERVER_PIPE_H
