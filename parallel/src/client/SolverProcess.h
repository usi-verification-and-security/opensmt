//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_PROCESSSOLVER_H
#define CLAUSE_SHARING_PROCESSSOLVER_H

#include "Settings.h"
#include "lib/Process.h"


class SolverProcess : public Process {
private:
    Socket *lemmas;
    std::map<std::string, std::string> header;

protected:
    void main();

public:
    SolverProcess(Socket *, std::map<std::string, std::string> &, std::string &);

    std::string toString();

    std::map<std::string, std::string> get_header() { return this->header; }

    static const char *solver;
    std::string instance;
};

#endif //CLAUSE_SHARING_PROCESSSOLVER_H
