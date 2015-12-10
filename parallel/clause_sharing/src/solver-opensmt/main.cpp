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


int main(int argc, char **argv) {
    Settings::Default.load(argc, argv);
    //Frame server = connect(Settings::Default.server.hostname, Settings::Default.server.port);

    ThreadSolver *solver = NULL;
    uint32_t length;
    char *frame;
    fd_set set;

    std::string s("a");
    std::string d("b");

    solver = new ThreadSolver(s, d);
    solver->start();

    while (1) {
        FD_ZERO(&set);
        //FD_SET(server.file_descriptor(), &set);
        if (solver != NULL)
            FD_SET(solver->reader().file_descriptor(), &set);
        if (select(FD_SETSIZE, &set, NULL, NULL, NULL) == -1)
            throw "Select error";

        if (solver != NULL && FD_ISSET(solver->reader().file_descriptor(), &set)) {
            std::string frame;
            length = solver->reader().read(frame);
            std::cout << (int)frame[0] << "\n";
            if (frame[0] != s_Undef.getValue()) {
                //server.write(frame);
                std::cout << (int)frame[0] << "\n";
            }
            delete solver;
            break;
        }

//        if (FD_ISSET(server.file_descriptor(), &set) != 0) {
//            std::string frame;
//            try {
//                server.read(frame);
//            } catch (FrameException ex) {
//                std::cout << "Server connection lost. Exit now.\n";
//                exit(0);
//            }
//        }

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
