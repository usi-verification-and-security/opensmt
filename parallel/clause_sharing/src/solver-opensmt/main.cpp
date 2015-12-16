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
            throw Exception("select error");

        if (solver != NULL && FD_ISSET(solver->reader().file_descriptor(), &set)) {
            solver->reader().read(frame);
            Message message;
            message.load(frame);
            frame.clear();
            frame.append(message.header["msg"].empty() ? "S" : "E");
            uint8_t i;
            for (i = 0; message.header["channel"][i] != '.' && i < (uint8_t) -1 &&
                        i < message.header["channel"].size(); i++) { }
            frame.append(message.header["channel"].substr(0, (size_t) i));
            frame.append("\\");
            frame.append(message.header["msg"].empty() ? message.header["status"] : message.header["msg"]);
            server.write(frame);
            delete solver;
            solver = NULL;
        }

        if (FD_ISSET(server.file_descriptor(), &set) != 0) {
            try {
                server.read(frame);
            } catch (FrameException) {
                throw Exception("Server connection lost. Exit now.");
            }
            std::string id, osmt2;
            switch (frame[0]) {
                case '!':
                    delete solver;
                    throw Exception("Server requested to stop. Exit now.");
                case 'S':
                    uint8_t i;
                    for (i = 2; frame[i] != '\\' && i < (uint8_t) -1 && i < frame.size(); i++) { }
                    id = frame.substr(1, (size_t) i - 1);
                    osmt2 = frame.substr(i + 1);
                    delete solver;
                    solver = new ProcessSolver(Settings::Default, id, osmt2);
                    break;
                case 'Q':
                    if (solver != NULL) {
                        delete solver;
                        solver = NULL;
                    }
                    break;
                default:
                    std::cerr << "warning: server sent invalid message.\n";
            }
        }

    }
}

class A {
public:
    A() { };

    void z() {
        this->f();
    }

    virtual void f() {
        std::cout << "A\n";
    }
};

class B : public A {
public:
    B() : A() { };
};

class C : public B {
public:
    C() : B() { };

    void f() {
        std::cout << "C\n";
    }
};


int main(int argc, char **argv) {
    try {
        Settings::Default.load(argc, argv);
        loop();
    }
    catch (FrameException ex) {
        std::cerr << "Frame exception: " << ex.what() << "\n";
    }
    catch (ProcessException ex) {
        std::cerr << "Process exception: " << ex.what() << "\n";
    }
    catch (Exception ex) {
        std::cerr << ex.what() << "\n";
    }
    catch (...) {
        std::cerr << "exception.\n";
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
