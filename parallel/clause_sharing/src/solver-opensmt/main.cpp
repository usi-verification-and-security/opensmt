//
// Created by Matteo Marescotti.
//

#include <lib/Log.h>
#include "main.h"


int main(int argc, char **argv) {
    Settings settings = Settings();
    std::map<std::string, std::string> header;
    std::string payload;

    try {
        settings.load(argc, argv);
    }
    catch (Exception ex) {
        std::cerr << "Invalid argument: " << ex.what() << "\n";
    }

    if (settings.server.port > 0) {
        Socket server = Socket(settings.server);
        ProcessSolver *solver = NULL;
        while (true) {
            server.read(header, payload);
            if (header.count("command") != 1)
                continue;
            if (header["command"] == "solve") {
                if (solver != NULL) {
                    solver->stop();
                    solver->join();
                    solver = NULL;
                }
                solver = new ProcessSolver(settings, header["name"], header["hash"], payload);
                
            }
        }
    }

    for (auto filename = settings.files.begin(); filename != settings.files.end(); ++filename) {
        std::ifstream file(*filename);
        if (!file.is_open()) {
            Log::log(Log::WARNING, "unable to open: " + *filename);
            continue;
        }

        std::string content;
        file.seekg(0, std::ios::end);
        content.resize((unsigned long) file.tellg());
        file.seekg(0, std::ios::beg);
        file.read(&content[0], content.size());
        file.close();

        ProcessSolver p(settings, *filename, "", content);
        p.reader()->read(header, payload);
        std::cout << payload << "\n";
        p.writer()->write(header, payload);
    }

    sleep(50);

}