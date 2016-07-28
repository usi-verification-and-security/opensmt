//
// Created by Matteo on 22/07/16.
//

#ifndef CLAUSE_SERVER_OPENSMTSOLVER_H
#define CLAUSE_SERVER_OPENSMTSOLVER_H

#include "SimpSMTSolver.h"
#include "Interpret.h"
#include "client/Settings.h"


namespace opensmt {
    extern bool stop;
}


class OpenSMTInterpret : public Interpret {
private:
    std::map<std::string, std::string> &header;
    Socket *clause_socket;
protected:
    void new_solver();

public:
    OpenSMTInterpret(std::map<std::string, std::string> &header, Socket *clause_socket, SMTConfig &c) :
            Interpret(c),
            header(header),
            clause_socket(clause_socket) { }

};

class OpenSMTSolver : public SimpSMTSolver {
private:
    static constexpr char clause_separator = '\n';
    static constexpr uint32_t clause_request = 100;
    std::map<std::string, std::string> &header;
    Socket *clause_socket;
    uint32_t trail_sent;

    void inline clausesPublish();

    void inline clausesUpdate();

public:
    OpenSMTSolver(std::map<std::string, std::string> &, Socket *, SMTConfig &, THandler &);

    ~OpenSMTSolver();
};


#endif //CLAUSE_SERVER_OPENSMTSOLVER_H
