//
// Created by Matteo on 02/12/15.
//

#include "ClauseSharing.h"

redisContext *ClauseSharing::Connect(const char *hostname, int port) {
    redisContext *context;
    redisReply *reply;
    struct timeval timeout = {1, 500000}; // 1.5 seconds

    /* CONNECT */
    context = redisConnectWithTimeout(hostname, port, timeout);
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

ClauseSharing::ClauseSharing(const char *channel) {
    this->thread = NULL;
    this->channel = std::string(channel);
    this->context_pub = ClauseSharing::Connect(Settings::Default->redis_hostname.c_str(),
                                               Settings::Default->redis_port);
    this->context_sub = ClauseSharing::Connect(Settings::Default->redis_hostname.c_str(),
                                               Settings::Default->redis_port);
}

void ClauseSharing::Start() {
    if (this->thread == NULL)
        *this->thread = std::thread(&ClauseSharing::heuristic, this);
    else
        throw "already started";
}

void ClauseSharing::Stop() {
    this->thread->join();
    exit(0);
}

void ClauseSharing::heuristic() {
    redisReply *reply = (redisReply *) redisCommand(context_pub, "DEL clauses");
    freeReplyObject(reply);

    /* MAIN LOOP */
    reply = (redisReply *) redisCommand(context_sub, "SUBSCRIBE clauses.out");
    freeReplyObject(reply);

    while (redisGetReply(context_sub, (void **) &reply) == REDIS_OK) {
        assert (reply->type == REDIS_REPLY_ARRAY && reply->elements == 3);
        assert (std::string(reply->element[0]->str).compare("message") == 0);

        channel = std::string(reply->element[1]->str);
        std::cout << "message on channel: " << channel << "\n";

        Message m;
        std::string s = std::string(reply->element[2]->str, (size_t) reply->element[2]->len);
        m.load(s);
        freeReplyObject(reply);

        // ===== Now I have the same message the client sent =====

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
            reply = (redisReply *) redisCommand(context_pub, "SADD clauses %b", str.c_str(), str.size());
            //if(reply->integer==0)
            //  std::cout << '!';
            freeReplyObject(reply);
        }


    }

    redisFree(context_pub);
    redisFree(context_sub);

}
