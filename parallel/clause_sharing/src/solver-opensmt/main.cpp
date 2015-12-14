//
// Created by Matteo Marescotti.
//

#include "main.h"


void print_clause(vec<Lit> &lits) {
    for (int i = 0; i < lits.size(); i++)
        std::cout << toInt(lits[i]) << ' ';
    std::cout << '\n';
}

int loop() {
    Frame server = Frame::connect(Settings::Default.server.hostname, Settings::Default.server.port);
    ProcessSolver *solver = NULL;
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
            Message m;
            m.load(frame);
            char *buffer = NULL;
            int buffer_length;
            if (m.header["msg"].empty())
                buffer_length = asprintf(&buffer,
                                         "S%s\\%d",
                                         solver->id.c_str(),
                                         (int) m.header["status"][0]
                );
            else
                buffer_length = asprintf(&buffer,
                                         "E%s\\%s",
                                         solver->id.c_str(),
                                         m.header["msg"].c_str()
                );
            if (buffer_length < 0) {
                throw "asprintf error";
            }
            server.write(buffer, (uint32_t) buffer_length);
            free(buffer);
            delete solver;
            solver = NULL;
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
                    channel = frame.substr(1, (size_t) i - 1);
                    osmt2 = frame.substr(i + 1);
                    if (solver != NULL) {
                        delete solver;
                    }
                    solver = new ProcessSolver(channel, osmt2);
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
    catch (FrameException ex) {
        std::cerr << ex.what() << "\n";
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
