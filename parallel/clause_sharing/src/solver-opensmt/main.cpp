//
// Created by Matteo Marescotti.
//

#include "main.h"


void print_clause(vec<Lit> &lits) {
    for (int i = 0; i < lits.size(); i++)
        std::cout << toInt(lits[i]) << ' ';
    std::cout << '\n';
}


Frame connect(std::string hostname, uint16_t port) {
    int sockfd;
    struct sockaddr_in serv_addr;
    struct hostent *he;

    if ((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
        throw "Socket init error";

    if ((he = gethostbyname(hostname.c_str())) == NULL)
        throw "Invalid hostname";

    bzero(&serv_addr, sizeof(serv_addr));
    memcpy(&serv_addr.sin_addr, he->h_addr_list[0], (size_t) he->h_length);
    serv_addr.sin_family = AF_INET;
    serv_addr.sin_port = htons(port);

    if (::connect(sockfd, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) != 0)
        throw "Connect error";

    return Frame(sockfd, true);
}

int loop() {
    Frame server = connect(Settings::Default.server.hostname, Settings::Default.server.port);
    ThreadSolver *solver = NULL;
    fd_set set;

    while (1) {
        std::string frame;
        FD_ZERO(&set);
        FD_SET(server.file_descriptor(), &set);
        if (solver != NULL)
            FD_SET(solver->reader().file_descriptor(), &set);
        if (select(FD_SETSIZE, &set, NULL, NULL, NULL) == -1)
            throw "Select error";

        if (solver != NULL && FD_ISSET(solver->reader().file_descriptor(), &set)) {
            solver->reader().read(frame);
            sstat status = toSstat((int) frame[0]);
            if (status != s_Undef)
                continue;

            delete solver;
            break;
        }

        if (FD_ISSET(server.file_descriptor(), &set) != 0) {
            try {
                server.read(frame);
            } catch (FrameException) {
                throw "Server connection lost. Exit now.";
            }
            std::string channel, osmt2;
            switch (frame[0]) {
                case '!':
                    throw "Server requested to stop. Exit now.";
                case 'S':
                    uint8_t i;
                    for (i = 2; frame[i] != '\\' && i < (uint8_t) -1 && i < frame.size(); i++) { }
                    channel = frame.substr(2, (size_t) i - 2);
                    osmt2 = frame.substr(i + 1);
                    if (solver != NULL)
                        delete solver;
                    solver = new ThreadSolver(channel, osmt2);
                    break;
                case 'Q':
                    if (solver != NULL) {
                        delete solver;
                        solver = NULL;
                    }
                    break;
                default:
                    std::cerr << "Warning: server sent invalid message.\n";
            }
        }

    }
}

int main(int argc, char **argv) {
    try {
        Settings::Default.load(argc, argv);
        loop();
    }
    catch (char const *ex) {
        std::cerr << ex << "\n";
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
