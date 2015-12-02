//
//  
//  
//
//  Created by Matteo on 20/02/15.
//
//

#include "net.h"
#include "Interpret.h"
#include "smtsolvers/CoreSMTSolver.h"

namespace opensmt {
    extern bool stop;
}

void error(const char *msg) {
    perror(msg);
    exit(0);
}

FrameSocket::FrameSocket(int sockfd) {
    this->sockfd = sockfd;
}

uint32_t FrameSocket::readn(char *buffer, uint32_t n) {
    uint32_t r = 0;
    while (n > r) {
        r += (uint32_t) ::read(this->sockfd, &buffer[r], n - r);
        if (r == 0)
            throw "Server connection broken";
    }
    return r;
}

uint32_t FrameSocket::read(char **frame) {
    uint32_t length = 0;
    uint8_t buffer[4];
    if (this->readn((char *) buffer, 4) != 4)
        return 0;
    length = (uint32_t) buffer[0] << 24 |
             (uint32_t) buffer[1] << 16 |
             (uint32_t) buffer[2] << 8 |
             (uint32_t) buffer[3];
    *frame = (char *)malloc(length);
    return this->readn(*frame, length);
}

uint32_t FrameSocket::write(char *frame, uint32_t length) {
    uint8_t buffer[4];
    buffer[3] = (uint8_t) length;
    buffer[2] = (uint8_t) (length >> 8);
    buffer[1] = (uint8_t) (length >> 16);
    buffer[0] = (uint8_t) (length >> 24);
    if (::write(this->sockfd, (char *) buffer, 4) != 4)
        return 0;
    return (uint32_t) ::write(this->sockfd, frame, length);
}


WorkerClient::WorkerClient() {
    int sockfd;
    struct sockaddr_in serv_addr;
    struct hostent *he;

    if ((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
        throw "Socket init";

    if ((he = gethostbyname(SMTConfig::server_host)) == NULL)
        throw "Invalid hostname";

    bzero(&serv_addr, sizeof(serv_addr));
    memcpy(&serv_addr.sin_addr, he->h_addr_list[0], he->h_length);
    serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(SMTConfig::server_port);

    if (connect(sockfd, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) != 0)
        throw "Connect error";

    this->s = new FrameSocket(sockfd);

    this->rpipe = NULL;
}

void WorkerClient::solve(int wpipefd, std::string &osmt2, uint32_t jid) {
    char buffer[128];

    std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
    std::random_device rd;
    SMTConfig config;
    config.setRandomSeed(randuint(rd));

    //Logic_t l = this->logic.getLogic();
    Theory *theory;
    //if (l == QF_UF)
    //    theory = new UFTheory(config);
    //else if (l == QF_LRA)
    theory = new LRATheory(config);
    //else {
    //    cerr << "Unsupported logic" << endl;
    //    exit(1);
    //}

    MainSolver *main_solver = new MainSolver(*theory, config);
    main_solver->initialize();

    char *msg;
    bool s = main_solver->readSolverState((int *)osmt2.c_str(), osmt2.size(), true, &msg);
    delete &osmt2;

    int n = 0;
    if(!s){
        n = snprintf(buffer, 128, "E%u\\%s", jid, msg);
    }
    else{
        std::cout << "Started job " << jid  << "\n";
        sstat status = main_solver->simplifyFormulas(&msg);
        if (status != s_True && status != s_False)
            status = main_solver->solve();
        if (!opensmt::stop) {
            n = snprintf(buffer, 128, "S%u\\%hhd", jid, status.getValue());
        }
        else {
            n = snprintf(buffer, 128, "!");
        }
    }

    FrameSocket *wpipe = new FrameSocket(wpipefd);

    wpipe->write(buffer, n);
    close(wpipe->fd());
    std::cout << "Finished job " << jid << "\n";
}

void WorkerClient::command(char *frame, uint32_t length) {
    uint32_t i, jid;
    int n;
    int file;
    int pipefd[2];
    char buffer[1024];

    if (frame[0] == '!') {
        exit(0);
    }

    for (i = 2; frame[i] != '\\' && i < 7 && i < length; i++) { }
    frame[i] = '\0';
    jid = atoi(&frame[1]);
    if (jid > 999999) {
        n = snprintf(buffer, 1024, "E%u\\invalid job id", jid);
        this->s->write(buffer, n);
        return;
    }

    if (frame[0] == 'S') {
        if (this->rpipe != NULL) {
            n = snprintf(buffer, 1024, "E%u\\already executing a job", this->jid);
            this->s->write(buffer, n);
            return;
        }

        if (pipe(pipefd) == -1) {
            n = snprintf(buffer, 1024, "E%u\\pipe error", this->jid);
            this->s->write(buffer, n);
            return;
        }

        this->jid = jid;
        this->rpipe = new FrameSocket(pipefd[0]);
        std::string *osmt2 = new std::string(&frame[i + 1], length - i + 1);
        this->t = std::thread(solve, pipefd[1], std::ref(*osmt2), this->jid);

        /*
        char filename[30] = "/tmp/fileXXXXXX";
        file = ::mkstemp(filename);

        ::write(file, &frame[i + 1], length - i - 1);
        ::close(file);

        std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
        std::random_device rd;
        n = snprintf(buffer, 1024, "(set-option :random-seed %u)\n"
                "(set-logic QF_LRA)\n"
                "(read-state \"%s\")\n"
                "(check-sat)\n", randuint(rd), filename);

        strcpy(filename, "/tmp/fileXXXXXX");
        file = ::mkstemp(filename);
        ::write(file, buffer, n);
        ::close(file);
        std::string str = std::string(filename) + std::string(".smt2");
        std::rename(filename, str.c_str());
        strcpy(filename, str.c_str());

        this->rpipe = new FrameSocket(pipefd[0]);
        this->t = std::thread(solve, pipefd[1], filename, this->jid);
        ::free(filename);
         */
    }
    else if (frame[0] == 'Q') {
        if (jid == this->jid) {
            opensmt::stop = true;
            this->t.join();
            opensmt::stop = false;
        }
    }
}

void WorkerClient::runForever() {
    uint32_t length;
    char *frame;
    fd_set set;

    while (1) {
        FD_ZERO(&set);
        FD_SET(this->s->fd(), &set);
        if (this->rpipe != NULL)
            FD_SET(this->rpipe->fd(), &set);
        if (select(FD_SETSIZE, &set, NULL, NULL, NULL) == -1)
            throw "Select";

        if (this->rpipe != NULL && FD_ISSET(this->rpipe->fd(), &set)) {
            length = this->rpipe->read(&frame);
            if (frame[0] != '!') {
                this->s->write(frame, length);
            }
            close(this->rpipe->fd());
            this->rpipe = NULL;
            free(frame);
        }

        if (FD_ISSET(this->s->fd(), &set) != 0) {
            try {
                length = this->s->read(&frame);
            }catch (char const *e) {
                std::cout << "Server connection lost. Exit now.\n";
                exit(0);
            }
            this->command(frame, length);
            free(frame);
        }

    }
}