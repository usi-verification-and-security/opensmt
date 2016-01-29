#include "main.h"


void print_clause(vec<Lit> &lits) {
    for (int i = 0; i < lits.size(); i++)
        std::cout << toInt(lits[i]) << ' ';
    std::cout << '\n';
}

redisContext *connect(std::string &hostname, uint16_t port) {
    redisContext *context;
    redisReply *reply;
    struct timeval timeout = {1, 500000}; // 1.5 seconds

    /* CONNECT */
    context = redisConnectWithTimeout(hostname.c_str(), port, timeout);
    if (context == NULL || context->err) {
        if (context) {
            std::string err = std::string("Connection error: ") + std::string(context->errstr);
            redisFree(context);
            throw Exception(err);
        } else {
            throw Exception("Connection error: can't allocate redis context");
        }
    }

    /* PING */
    reply = (redisReply *) redisCommand(context, "PING");
    if (reply == NULL) {
        throw Exception("PING to the server failed");
    }
    freeReplyObject(reply);

    return context;
}

int main(int argc, char **argv) {
//    try {
        Settings::Default.load(argc, argv);
//        Heuristic *cs = new Heuristic(Settings::Default.redis.hostname,
//                                      Settings::Default.redis.port);
//        cs->join();
//    }
//    catch (FrameException ex) {
//        std::cerr << "Frame exception: " << ex.what() << "\n";
//    }
//    catch (Exception ex) {
//        std::cerr << ex.what() << "\n";
//    }


    redisContext *context_pub = connect(Settings::Default.redis.hostname,
                                      Settings::Default.redis.port);
    redisContext *context_sub = connect(Settings::Default.redis.hostname,
                                      Settings::Default.redis.port);
    redisReply *reply;
//    reply = (redisReply *) redisCommand(context_pub, "KEYS clauses.*");
//    if (reply == NULL)
//        throw Exception("redis error");
//    for (size_t i = 0; i < reply->elements; i++) {
//        redisReply *reply_del = (redisReply *) redisCommand(context_pub, "DEL %s", reply->element[i]->str);
//        freeReplyObject(reply_del);
//    }
//    freeReplyObject(reply);

    reply = (redisReply *) redisCommand(context_sub, "PSUBSCRIBE clauses.*");
    freeReplyObject(reply);
    while (redisGetReply(context_sub, (void **) &reply) == REDIS_OK) {
        assert (reply->type == REDIS_REPLY_ARRAY && reply->elements == 4);
        assert (std::string(reply->element[0]->str).compare("pmessage") == 0);

        std::string channel = std::string(reply->element[2]->str, reply->element[2]->len);

        Message m;
        std::string s = std::string(reply->element[3]->str, (size_t) reply->element[3]->len);
        m.load(s);
        freeReplyObject(reply);

        uint32_t o = 0;
        while (o < m.payload.length()) {
            vec<Lit> lits;
            clauseDeserialize(m.payload, &o, lits);
            if (lits.size() <= 0 || lits.size() > 5) {
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
            if (reply != NULL)
                freeReplyObject(reply);
        }

        reply = (redisReply *) redisCommand(context_pub, "ttl %s", channel.c_str());
        if (reply != NULL) {
            int ttl = reply->integer;
            freeReplyObject(reply);
            if(ttl<0){
                reply = (redisReply *) redisCommand(context_pub, "expire %s 1010", channel.c_str());
                if (reply != NULL)
                    freeReplyObject(reply);
            }
        }

    }

}




/* int *f;
j = redisBufferWrite(c, f);

j = 0;
while (redisGetReplyFromReader(c, (void **) &reply) == REDIS_OK) {
    redisBufferRead(c);
    if (reply == NULL) {
        if (j++ == 10000000) {
            j = 0;
            printf(".");
            fflush(stdout);
        }
        continue;
    }
    printf("\n");
    for (j = 0; j < reply->elements; j++) {
        printf("%u) %s\n", j, reply->element[j]->str);
    }
    freeReplyObject(reply);
} */
