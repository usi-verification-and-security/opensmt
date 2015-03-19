//
//  
//  
//
//  Created by Matteo on 20/02/15.
//
//

#include "net.h"
#include "Interpret.h"

namespace opensmt { extern bool stop; }


void error(const char *msg)
{
    perror(msg);
    exit(0);
}

FrameSocket::FrameSocket(int sockfd){
    this->sockfd=sockfd;
}

uint32_t FrameSocket::readn(char *buffer, uint32_t n){
    uint32_t r=0;
    while (n>r) {
        r+=(uint32_t)::read(this->sockfd, &buffer[r], n-r);
    }
    return r;
}

uint32_t FrameSocket::read(char **frame){
    uint32_t length = 0;
    uint8_t buffer[4];
    if(this->readn((char*)buffer, 4) != 4)
        return 0;
    length = (uint32_t)buffer[0]<<24 |
                (uint32_t)buffer[1]<<16 |
                (uint32_t)buffer[2]<<8 |
                (uint32_t)buffer[3];
    *frame = new char[length];
    return this->readn(*frame, length);
}

uint32_t FrameSocket::write(char *frame, uint32_t length){
    uint8_t buffer[4];
    buffer[3]=(uint8_t)length;
    buffer[2]=(uint8_t)(length>>8);
    buffer[1]=(uint8_t)(length>>16);
    buffer[0]=(uint8_t)(length>>24);
    if(::write(this->sockfd, (char*)buffer, 4)!=4)
        return 0;
    return (uint32_t)::write(this->sockfd, frame, length);
}

WorkerClient::WorkerClient(char *host, uint16_t port){
    int sockfd;
    struct sockaddr_in serv_addr;
    struct hostent *he;
    
    if((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
        throw "Socket init";
    
    if((he = gethostbyname(host)) == NULL)
        throw "Invalid hostname";
    
    bzero(&serv_addr, sizeof(serv_addr));
    memcpy(&serv_addr.sin_addr, he->h_addr_list[0], he->h_length);
    serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(port);
    
    if(connect(sockfd, (struct sockaddr*)&serv_addr, sizeof(serv_addr)) != 0)
        throw "Connect error";
    
    this->s = new FrameSocket(sockfd);
    
    this->rpipe=NULL;
}

void WorkerClient::solve(int wpipefd, char* smt2filename, uint32_t jid){
    char buffer[128];
    int n=0;
    Interpret interpreter;
    FILE *fin;
    FrameSocket *wpipe = new FrameSocket(wpipefd);
    sstat status;
    
    if((fin = fopen(smt2filename, "rt" )) == NULL){
        n=snprintf(buffer, 128, "E%u\\can't open file", jid);
    }
    else{
        std::cout << "Started job " << jid << ": "<< smt2filename<<"\n";
        interpreter.interpFile(fin);
        fclose(fin);
        if(!opensmt::stop){
            status = interpreter.main_solver.getStatus();
            n=snprintf(buffer, 128, "S%u\\%hhd", jid, status.getValue());
        }
        else{
            opensmt::stop=false;
        }
    }
    
    if(n>0)
        wpipe->write(buffer, n);
    close(wpipe->fd());
    std::cout << "Finished job " << jid << "\n";
}

void WorkerClient::command(char *frame, uint32_t length){
    uint32_t i, jid;
    int n;
    char *filename;
    FILE *file;
    int pipefd[2];
    char buffer[1024];
    
    if(frame[0]=='S'){
        for(i=2;frame[i]!='\\' && i<7;i++){}
        frame[i]='\0';
        jid = atoi(&frame[1]);
        if (jid>999999){
            n=snprintf(buffer, 1024, "E%u\\invalid job id", jid);
            this->s->write(buffer, n);
            return;
        }
        
        if(this->rpipe!=NULL){
            n=snprintf(buffer, 1024, "E%u\\already executing a job", jid);
            this->s->write(buffer, n);
            return;
        }
        
        if (pipe(pipefd) == -1) {
            n=snprintf(buffer, 1024, "E%u\\pipe error", jid);
            this->s->write(buffer, n);
            return;
        }
        
        filename = tmpnam(NULL);
        file = fopen(filename, "w");
        ::fwrite(&frame[i+1], sizeof(char), length-i-1, file);
        fclose(file);
        
        n=snprintf(buffer, 1024, "(set-option :random-seed 16)\n"
                   "(set-logic QF_UF)\n"
                   "(read-state \"%s\")\n"
                   "(check-sat)\n", filename);
        
        filename = tmpnam(NULL);
        file = fopen(filename, "w");
        ::fwrite(buffer, sizeof(char), n, file);
        fclose(file);
        
        this->rpipe = new FrameSocket(pipefd[0]);
        this->t = std::thread(solve, pipefd[1], filename, jid);
    }
}

void WorkerClient::runForever(){
    uint32_t length;
    char *frame;
    fd_set set;

    while (1) {
        FD_ZERO(&set);
        FD_SET(this->s->fd(), &set);
        if(this->rpipe!=NULL)
            FD_SET(this->rpipe->fd(), &set);
        
        if(select(FD_SETSIZE, &set, NULL, NULL, NULL)==-1)
            throw "Select";
        
        if(FD_ISSET(this->s->fd(), &set)!=0){
            length = this->s->read(&frame);
            this->command(frame, length);
            free(frame);
        }
        
        if(this->rpipe!=NULL && FD_ISSET(this->rpipe->fd(), &set)){
            length = this->rpipe->read(&frame);
            this->s->write(frame, length);
            
            close(this->rpipe->fd());
            this->rpipe=NULL;
            free(frame);
        }
    }
}