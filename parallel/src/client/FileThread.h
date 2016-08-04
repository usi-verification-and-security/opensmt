//
// Created by Matteo on 22/07/16.
//

#ifndef CLAUSE_SERVER_FILETHREAD_H
#define CLAUSE_SERVER_FILETHREAD_H

#include "lib/Thread.h"
#include "Settings.h"


class FileThread : public Thread {
private:
    Settings &settings;
    Socket *server;

protected:
    void main();

public:
    FileThread(Settings &);

    ~FileThread();

};


#endif //CLAUSE_SERVER_FILETHREAD_H
