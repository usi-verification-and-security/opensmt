//
// Created by Matteo Marescotti.
//

#ifndef CLAUSE_SHARING_PROTOCOL_H
#define CLAUSE_SHARING_PROTOCOL_H

#include <map>
#include <string>
#include "SolverTypes.h"

class Message {
private:

public:
    std::map<std::string, std::string> header;
    std::string payload;

    Message() { };

    void dump(std::string &s);

    void load(std::string &s);

};

void clauseSerialize(Clause &c, std::string &s);

void clauseDeserialize(std::string &s, uint32_t *o, vec<Lit> &lits);



#endif //CLAUSE_SHARING_PROTOCOL_H
