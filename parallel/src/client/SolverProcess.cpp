//
// Created by Matteo on 29/08/16.
//

#include <unistd.h>
#include <fcntl.h>
#include <iostream>
#include <random>
#include "SolverProcess.h"


SolverProcess::SolverProcess(Socket *lemmas, std::map<std::string, std::string> header, std::string instance) :
        lemmas(lemmas),
        header(header),
        instance(instance) {
    if (this->header.count("seed") == 0) {
        std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
        std::random_device rd;
        this->header["seed"] = std::to_string(randuint(rd));
    }
    if (this->header.count("lemmas") == 0) {
        this->header["lemmas"] = std::to_string(1000);
    }
    this->start();
}

void SolverProcess::main() {

    if (this->header.count("stderr") == 0)
        this->header["stderr"] = "/dev/null";
    if (this->header["stderr"] != "-") {
        FILE *file = fopen(this->header["stderr"].c_str(), "a+");
        dup2(fileno(file), fileno(stderr));
        fclose(file);
    }

    if (this->header.count("stdout") == 0)
        this->header["stdout"] = "/dev/null";
    if (this->header["stdout"] != "-") {
        FILE *file = fopen(this->header["stdout"].c_str(), "a+");
        dup2(fileno(file), fileno(stdout));
        fclose(file);
    }

    this->header["status"] = this->solve();
    this->writer()->write(this->header, "");

}