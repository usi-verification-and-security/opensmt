#include "main.h"

void print_clause(vec<Lit> &lits) {
    for (int i = 0; i < lits.size(); i++)
        std::cout << toInt(lits[i]) << ' ';
    std::cout << '\n';
}


int main(int argc, char **argv) {
    auto cs = new ClauseSharing((char *)"clauses", (char *)Settings::Default.redis_hostname.c_str(), Settings::Default.redis_port);
    cs->Start();
    std::this_thread::sleep_for(std::chrono::milliseconds(1000));
    cs->Stop();
    std::cout << "esco anche io\n";

    delete cs;
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
