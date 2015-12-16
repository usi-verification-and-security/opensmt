//
// Created by Matteo on 10/12/15.
//

#include "main.h"


_SMTSolver::_SMTSolver(Settings &s, std::string &channel, SMTConfig &c, THandler &t) :
        SimpSMTSolver(c, t), channel(channel), cls_pub(NULL), cls_sub(NULL) {
    if (s.clause_sharing) {
        if (this->channel.size() <= 0)
            throw Exception("channel empty");
        struct timeval timeout = {1, 500000}; // 1.5 seconds
        this->cls_pub = redisConnectWithTimeout(s.redis.hostname.c_str(),
                                                s.redis.port,
                                                timeout);
        this->cls_sub = redisConnectWithTimeout(s.redis.hostname.c_str(),
                                                s.redis.port,
                                                timeout);
        if (this->cls_pub == NULL || this->cls_sub == NULL) {
            redisFree(this->cls_pub);
            redisFree(this->cls_sub);
            throw Exception("redis error");
        }
    }
}

_SMTSolver::~_SMTSolver() {
    redisFree(this->cls_pub);
    redisFree(this->cls_sub);
}

void _SMTSolver::clausesPublish() {
    if (this->cls_pub == NULL)
        return;
    std::string s;
    uint32_t clauses_sent=0;
    for (int i = 0; i < this->learnts.size(); i++) {
        Clause &c = *this->learnts[i];
        if (c.mark() != 3) {
            clauses_sent++;
            clauseSerialize(c, s);
            c.mark(3);
        }
    }
    if (s.length() == 0)
        return;
    Message m;

    struct sockaddr_in sin;
    int addrlen = sizeof(sin);
    getsockname(this->cls_pub->fd, (struct sockaddr *) &sin, (socklen_t *) &addrlen);
    m.header["from"].append(inet_ntoa(sin.sin_addr));
    m.header["from"].append(":");
    m.header["from"].append(std::to_string(sin.sin_port));

    m.payload = s;
    std::string d;
    m.dump(d);

    redisReply *reply = (redisReply *) redisCommand(this->cls_pub, "PUBLISH clauses.%s %b",
                                                    this->channel.c_str(),
                                                    d.c_str(),
                                                    d.length());
    if (reply == NULL || reply->type == REDIS_REPLY_ERROR) {
        std::cerr << "error during clause publishing\n";
        freeReplyObject(reply);
//        redisFree(this->cls_pub);
//        this->cls_pub = NULL;
        return;
    }
    freeReplyObject(reply);
    std::cerr << "published\t" << clauses_sent << "\tclauses\n";
    /* non block
    redisCommand(this->c_cls_pub, "PUBLISH %s.out %b", this->channel, d.c_str(), d.length());
    this->flush(this->c_cls_pub);
    if (this->c_cls_pub->err != 0)
        cerr << "Redis publish connection lost\n"; */
}

void _SMTSolver::clausesUpdate() {
    if (this->cls_sub == NULL)
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
    redisReply *reply = (redisReply *) redisCommand(this->cls_sub, "SRANDMEMBER clauses.%s 10000",
                                                    this->channel.c_str());
    if (reply == NULL || reply->type == REDIS_REPLY_ERROR) {
        std::cerr << "error during clause updating\n";
        freeReplyObject(reply);
//        redisFree(this->cls_pub);
//        this->cls_pub = NULL;
        return;
    }
    if (reply->type != REDIS_REPLY_ARRAY) {
        freeReplyObject(reply);
        return;
    }

    for (int i = this->n_clauses; i < this->clauses.size(); i++) {
        if (i < this->n_clauses + reply->elements)
            this->removeClause(*this->clauses[i]);
        if (i + reply->elements < this->clauses.size())
            this->clauses[i] = this->clauses[i + reply->elements];
    }
    this->clauses.shrink(std::min(this->clauses.size() - this->n_clauses, (uint32_t) reply->elements));


    for (int i = 0; i < reply->elements; i++) {
        std::string str = std::string(reply->element[i]->str, reply->element[i]->len);
        vec<Lit> lits;
        uint32_t o = 0;
        clauseDeserialize(str, &o, lits);
        bool f = false;
        for (int j = 0; j < lits.size(); j++) {
            if (!this->var_seen[var(lits[j])]) {
                f = true;
                break;
            }
        }
        if (!f)
            this->addClause(lits, true);
    }

    std::cerr << "updated\t\t" << reply->elements << "\tclauses\n";
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


ProcessSolver::ProcessSolver(Settings &settings, std::string &channel, std::string &osmt2) :
        Process(), channel(channel), osmt2(osmt2), settings(settings) {
    this->start();
}

void ProcessSolver::main() {
    std::cerr << "Started job " << this->channel << "\n";

    sstat status = s_Undef;
    char *msg = NULL;

    std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
    std::random_device rd;
    SMTConfig config;
    config.setRandomSeed(randuint(rd));

    Theory *theory = new LRATheory(config);

    MainSolver *solver = NULL;
    try {
        solver = new MainSolver(
                *theory,
                config,
                new _SMTSolver(this->settings, this->channel, config, theory->getTHandler()));
    }
    catch (Exception ex) {
        msg = strdup(ex.what());
        goto done;
    }

    solver->initialize();
    if (solver->readSolverState((int *) this->osmt2.c_str(), (int) this->osmt2.size(), true, &msg)) {
        status = solver->simplifyFormulas(&msg);
        if (status != s_True && status != s_False)
            status = solver->solve();
    }

    delete solver;

    done:

    Message message;
    message.header["status"] = std::to_string((int) status.getValue());
    message.header["msg"] = msg == NULL ? std::string() : std::string(msg);
    message.header["channel"] = this->channel;
    std::string s;
    message.dump(s);
    this->writer().write(s);
    free(msg);

    std::cout << "Finished job\n";

}
