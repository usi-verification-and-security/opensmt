//
//  net.h
//  
//
//  Created by Matteo Marescotti on 20/02/15.
//
//

#include <iostream>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <sys/socket.h>
#include <netdb.h>
#include <unistd.h>
#include <errno.h>
#include <strings.h>
#include <string.h>
#include <thread>

class FrameSocket {
private:
    int sockfd;

public:
    FrameSocket(int sockfd);
    uint32_t readn(char *buffer, uint32_t length);
    uint32_t read(char **frame);
    uint32_t write(char *frame, uint32_t length);
    int fd(){return this->sockfd;}
};

class WorkerClient {
private:
    FrameSocket *s;
    FrameSocket *rpipe;
    std::thread t;
    void command(char *frame, uint32_t length);
    static void solve(int wpipefd, char* osmt2filename, uint32_t jid);
    
public:
    WorkerClient(char *host, uint16_t port);
    void runForever();
};