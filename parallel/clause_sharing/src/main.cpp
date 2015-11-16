#include "main.h"

redisContext *connect(const char *hostname, int port) {
    redisContext *context;
    redisReply *reply;
    struct timeval timeout = {1, 500000}; // 1.5 seconds

    /* CONNECT */
    context = redisConnectWithTimeout(hostname, port, timeout);
    if (context == NULL || context->err) {
        if (context) {
            std::cerr << "Connection error: " << context->errstr << "\n";
            redisFree(context);
        } else {
            std::cerr << "Connection error: can't allocate redis context\n";
        }
        exit(1);
    }

    /* PING server */
    reply = (redisReply *) redisCommand(context, "PING");
    if (reply == NULL) {
        std::cerr << "PING to the server failed\n";
        exit(1);
    }
    freeReplyObject(reply);

    return context;
}


void print_clause(vec<Lit> &lits) {
    for (int i = 0; i < lits.size(); i++)
        std::cout << toInt(lits[i]) << ' ';
    std::cout << '\n';
}


int main(int argc, char **argv) {
    redisContext *context_pub;
    redisContext *context_sub;
    redisReply *reply;
    std::string channel;
    const char *hostname = "*";
    int port = 6379;

    context_pub = connect(hostname, port);
    context_sub = connect(hostname, port);


    reply = (redisReply *) redisCommand(context_pub, "DEL clauses");
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
            if (lits.size() <= 0 || lits.size() > 10)
                continue;
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

    return 0;
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