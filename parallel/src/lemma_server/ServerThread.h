//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_SERVERTHREAD_H
#define CLAUSE_SHARING_SERVERTHREAD_H

#include "lib/Thread.h"
#include "lib/Net.h"
#include "Settings.h"


// thread to handle the connection with the server
class ServerThread : public Thread {
private:
    Settings &settings;
    Socket *server;

protected:
    void main();

public:
    ServerThread(Settings &);

    ~ServerThread();

};

#endif //CLAUSE_SHARING_SERVERTHREAD_H
