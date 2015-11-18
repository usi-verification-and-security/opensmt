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

std::string NetCfg::server_host;
uint16_t NetCfg::server_port = 0;
std::string NetCfg::database_host;
uint16_t NetCfg::database_port = 0;


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
    *frame = new char[length];
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

    if ((he = gethostbyname(NetCfg::server_host.c_str())) == NULL)
        throw "Invalid hostname";

    bzero(&serv_addr, sizeof(serv_addr));
    memcpy(&serv_addr.sin_addr, he->h_addr_list[0], he->h_length);
    serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(NetCfg::server_port);

    if (connect(sockfd, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) != 0)
        throw "Connect error";

    this->s = new FrameSocket(sockfd);

    this->rpipe = NULL;
}

void WorkerClient::solve(int wpipefd, char *smt2filename, uint32_t jid) {
    char buffer[128];
    int n = 0;
    SMTConfig c;
    Interpret interpreter(c);
    FILE *fin;
    FrameSocket *wpipe = new FrameSocket(wpipefd);
    sstat status;

    if ((fin = fopen(smt2filename, "r")) == NULL) {
        n = snprintf(buffer, 128, "E%u\\can't open file", jid);
    }
    else {
        std::cout << "Started job " << jid << ": " << smt2filename << "\n";
        interpreter.interpFile(fin);
        fclose(fin);
        if (!opensmt::stop) {
            status = interpreter.main_solver->getStatus();
            n = snprintf(buffer, 128, "S%u\\%hhd", jid, status.getValue());
        }
        else {
            n = snprintf(buffer, 128, "!");
        }
    }

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
            length = this->s->read(&frame);
            this->command(frame, length);
            free(frame);
        }

    }
}


Sharing::Sharing() {
    this->c_cls_pub = NULL;
    this->c_cls_sub = NULL;
    this->channel = NULL;
}

Sharing::~Sharing() {
    this->reset(NULL);
}

inline void Sharing::inet_source(int fd, std::string &str) {
    struct sockaddr_in sin;
    int addrlen = sizeof(sin);
    getsockname(fd, (struct sockaddr *) &sin, (socklen_t *) &addrlen);
    str.append(inet_ntoa(sin.sin_addr));
    str.append(":");
    str.append(std::to_string(sin.sin_port));
}

void Sharing::reset(char *channel) {
    free(this->channel);
    if (channel == NULL || NetCfg::database_host.empty()) {
        redisFree(this->c_cls_pub);
        redisFree(this->c_cls_sub);
        return;
    }
    this->channel = (char *) malloc(strlen(channel));
    strcpy(this->channel, channel);
    if (this->c_cls_pub == NULL)
        this->c_cls_pub = this->connect();
    if (this->c_cls_sub == NULL)
        this->c_cls_sub = this->connect();
    /*  non block
    redisCommand(this->c_cls_sub, "SUBSCRIBE %s.in", this->channel);
    this->flush(this->c_cls_sub);
    do {
        if (redisBufferRead(this->c_cls_sub) != REDIS_ERR)
            redisGetReply(this->c_cls_sub, (void **) &reply);
        else {
            cerr << "Redis subscribe connection lost\n";
            break;
        }
    } while (reply == NULL);
    freeReplyObject(reply); */
}


redisContext *Sharing::connect() {
    redisContext *context;
    struct timeval timeout = {1, 500000}; // 1.5 seconds
    context = redisConnectWithTimeout(NetCfg::database_host.c_str(), NetCfg::database_port, timeout);
    if (context == NULL || context->err) {
        if (context) {
            std::cerr << "Connection error: " << context->errstr << "\n";
            redisFree(context);
        } else {
            std::cerr << "Connection error: can't allocate redis context\n";
        }
        return NULL;
    }

    return context;
}


void Sharing::flush(redisContext *context) {
    int wdone = 0;
    do {
        if (redisBufferWrite(context, &wdone) == REDIS_ERR)
            return;
    } while (!wdone);
}


void Sharing::clausesPublish(CoreSMTSolver &solver) {
    if (this->channel == NULL || this->c_cls_pub->err != 0)
        return;
    std::string s;
    for (int i = 0; i < solver.learnts.size(); i++) {
        Clause &c = *solver.learnts[i];
        if (c.mark() != 3) {
            clauseSerialize(c, s);
            c.mark(3);
        }
    }
    if (s.length() == 0)
        return;
    Message m;

    Sharing::inet_source(this->c_cls_pub->fd, m.header["from"]);

    m.payload = s;
    std::string d;
    m.dump(d);

    redisReply *reply = (redisReply *) redisCommand(this->c_cls_pub, "PUBLISH %s.out %b", this->channel, d.c_str(),
                                                    d.length());
    if (reply == NULL)
        std::cerr << "Connection error during clause publishing\n";
    freeReplyObject(reply);
    /* non block
    redisCommand(this->c_cls_pub, "PUBLISH %s.out %b", this->channel, d.c_str(), d.length());
    this->flush(this->c_cls_pub);
    if (this->c_cls_pub->err != 0)
        cerr << "Redis publish connection lost\n"; */
}


void Sharing::clausesUpdate(CoreSMTSolver &solver) {
    if (this->channel == NULL || this->c_cls_sub->err != 0)
        return;

    /* non block
    redisReply *reply;
    redisBufferRead(this->c_cls_sub);
    if (redisGetReplyFromReader(this->c_cls_sub, (void **) &reply) != REDIS_OK)
        cerr << "Redis subscribe connection lost\n";
    if (reply == NULL)
        return;
    assert (reply->type == REDIS_REPLY_ARRAY && reply->elements == 3);
    assert (std::string(reply->element[0]->str).compare("message") == 0);
    std::string s = std::string(reply->element[2]->str, reply->element[2]->len); */
//ZREVRANGEBYSCORE %s +inf 0 LIMIT 0 10000
    redisReply *reply = (redisReply *) redisCommand(this->c_cls_pub, "SRANDMEMBER %s 10000",
                                                    this->channel);
    if (reply == NULL) {
        std::cerr << "Connection error during clause updating\n";
        return;
    }
    if (reply->type != REDIS_REPLY_ARRAY)
        return;

    for (int i = solver.n_clauses; i < solver.clauses.size(); i++) {
        if (i < solver.n_clauses + reply->elements)
            solver.removeClause(*solver.clauses[i]);
        if (i + reply->elements < solver.clauses.size())
            solver.clauses[i] = solver.clauses[i + reply->elements];
    }
    solver.clauses.shrink(std::min(solver.clauses.size() - solver.n_clauses, (uint32_t) reply->elements));


    for (int i = 0; i < reply->elements; i++) {
        std::string str = std::string(reply->element[i]->str, reply->element[i]->len);
        vec<Lit> lits;
        uint32_t o = 0;
        clauseDeserialize(str, &o, lits);
        solver.addClause(lits, true);
    }
/*
    if (reply->type != REDIS_REPLY_STRING)
        return;
    std::string s = std::string(reply->str, reply->len);
    Message m;
    m.load(s);
    //if (m.header.find("from") != m.header.end()) if (m.header["from"].compare(...) == 0)
    //  return;
    uint32_t o = 0;
    while (o < m.payload.length()) {
        vec<Lit> lits;
        clauseDeserialize(m.payload, &o, lits);
        solver.addClause(lits, true);
    }
*/
    freeReplyObject(reply);
}
