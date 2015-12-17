#include "main.h"


void print_clause(vec<Lit> &lits) {
    for (int i = 0; i < lits.size(); i++)
        std::cout << toInt(lits[i]) << ' ';
    std::cout << '\n';
}


int main(int argc, char **argv) {
    try {
        Settings::Default.load(argc, argv);
        Heuristic *cs = new Heuristic(Settings::Default.redis.hostname,
                                      Settings::Default.redis.port);
        cs->join();
    }
    catch (FrameException ex) {
        std::cerr << "Frame exception: " << ex.what() << "\n";
    }
    catch (Exception ex) {
        std::cerr << ex.what() << "\n";
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
