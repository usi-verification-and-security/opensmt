//
// Created by Matteo Marescotti on 02/12/15.
//

#include "main.h"


redisContext *Heuristic::Connect(std::string &hostname, uint16_t port) {
    redisContext *context;
    redisReply *reply;
    struct timeval timeout = {1, 500000}; // 1.5 seconds

    /* CONNECT */
    context = redisConnectWithTimeout(hostname.c_str(), port, timeout);
    if (context == NULL || context->err) {
        if (context) {
            redisFree(context);
            throw "Connection error"; // << context->errstr << "\n";
        } else {
            throw "Connection error: can't allocate redis context";
        }
    }

    /* PING */
    reply = (redisReply *) redisCommand(context, "PING");
    if (reply == NULL) {
        throw "PING to the server failed";
    }
    freeReplyObject(reply);

    return context;
}

Heuristic::Heuristic(std::string &hostname, uint16_t port) :
        Thread() {
    this->context_pub = Heuristic::Connect(hostname, port);
    this->context_sub = Heuristic::Connect(hostname, port);
    redisReply *reply = (redisReply *) redisCommand(context_pub, "KEYS clauses.*");
    if (reply == NULL)
        throw "redis error";
    for (size_t i = 0; i < reply->elements; i++) {
        redisReply *reply_del = (redisReply *) redisCommand(context_pub, "DEL %s", reply->element[i]->str);
        freeReplyObject(reply_del);
    }
    freeReplyObject(reply);
    this->start();
}

Heuristic::~Heuristic() {
    redisFree(this->context_pub);
    redisFree(this->context_sub);
}

void Heuristic::main() {
    redisReply *reply;
    reply = (redisReply *) redisCommand(context_sub, "PSUBSCRIBE clauses.*");
    freeReplyObject(reply);
    while (redisGetReply(context_sub, (void **) &reply) == REDIS_OK) {
        assert (reply->type == REDIS_REPLY_ARRAY && reply->elements == 4);
        assert (std::string(reply->element[0]->str).compare("pmessage") == 0);

        std::string channel = std::string(reply->element[2]->str, reply->element[2]->len);
        //std::cout << "message on channel: " << channel << "\n";

        Message m;
        std::string s = std::string(reply->element[3]->str, (size_t) reply->element[3]->len);
        m.load(s);
        freeReplyObject(reply);

        uint32_t o = 0;
        while (o < m.payload.length()) {
            vec<Lit> lits;
            clauseDeserialize(m.payload, &o, lits);
            if (lits.size() <= 0 || lits.size() > 50) {
                continue;
            }
            sort(lits);
            std::string str;
            clauseSerialize(lits, str);
            //ZADD clauses NX %d %b
            reply = (redisReply *) redisCommand(context_pub, "SADD %s %b", channel.c_str(), str.c_str(),
                                                str.size());
            //if(reply->integer==0)
            //  std::cout << '!';
            freeReplyObject(reply);
        }
    }
}
