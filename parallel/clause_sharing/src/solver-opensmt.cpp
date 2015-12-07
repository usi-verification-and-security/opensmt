#include "solver-opensmt.h"


void print_clause(vec<Lit> &lits) {
    for (int i = 0; i < lits.size(); i++)
        std::cout << toInt(lits[i]) << ' ';
    std::cout << '\n';
}

ClauseSharing *cs;

int main(int argc, char **argv) {

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

    ClauseSharing *cs = new ClauseSharing((char *) "clauses", (char *) Settings::Default.redis_hostname.c_str(),
                                          Settings::Default.redis_port);
    cs->Start();
    std::this_thread::sleep_for(std::chrono::milliseconds(1000));
    ClauseSharing *cs1 = new ClauseSharing((char *) "clauses", (char *) Settings::Default.redis_hostname.c_str(),
                                           Settings::Default.redis_port);
    cs1->Start();
    std::this_thread::sleep_for(std::chrono::milliseconds(1000));
    cs->Stop();
    cs1->Join();
    delete cs;
    delete cs1;
    std::cout << "asd\n";
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
