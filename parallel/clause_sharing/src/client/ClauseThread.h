//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_CLAUSETHREAD_H
#define CLAUSE_SHARING_CLAUSETHREAD_H

#include "lib/Thread.h"
#include "lib/Net.h"


class ClauseThread : public Thread {
private:
    void log(uint8_t level, std::string message);

    Address address;
    Socket *socket;

protected:
    void main();

public:
    ClauseThread(Address);

    ~ClauseThread();

};

#endif //CLAUSE_SHARING_CLAUSETHREAD_H
