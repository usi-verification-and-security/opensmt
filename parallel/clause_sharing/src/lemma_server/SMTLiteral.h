//
// Created by Matteo on 27/07/16.
//

#ifndef CLAUSE_SERVER_SMTLITERAL_H
#define CLAUSE_SERVER_SMTLITERAL_H

#include <string>


class SMTLiteral {
private:
    int score;
public:
    SMTLiteral(std::string smtlib) :
            score(0),
            smtlib(smtlib) { }

    void increase() { //this->score = (this->score + 1) - this->score == 1 ? this->score + 1 : this->score;
        this->score++;
    }

    void decrease() { this->score--; }

    bool operator==(SMTLiteral const &b) const { return this->smtlib == b.smtlib; }

    bool operator!=(SMTLiteral const &b) const { return this->smtlib != b.smtlib; }

    bool operator<(SMTLiteral const &b) const { return this->score < b.score; }

    bool operator>(SMTLiteral const &b) const { return this->score > b.score; }

    bool operator<=(SMTLiteral const &b) const { return this->score <= b.score; }

    bool operator>=(SMTLiteral const &b) const { return this->score >= b.score; }

    std::string smtlib;
};


#endif //CLAUSE_SERVER_SMTLITERAL_H
