//
// Created by Matteo on 27/07/16.
//

#ifndef CLAUSE_SERVER_SMTLITERAL_H
#define CLAUSE_SERVER_SMTLITERAL_H

#include <string>
#include <list>


class Lemma {
private:
    int score;
public:
    Lemma(std::string smtlib) :
            score(0),
            smtlib(smtlib) { }

    static bool compare(const Lemma *const &a, Lemma *const &b) {
        return a->score < b->score;
    }

    void increase() { //this->score = (this->score + 1) - this->score == 1 ? this->score + 1 : this->score;
        this->score++;
    }

    void decrease() { this->score--; }

    inline int get_score() { return this->score; }

    bool operator==(Lemma const &b) const { return this->smtlib == b.smtlib; }

    bool operator!=(Lemma const &b) const { return this->smtlib != b.smtlib; }

    bool operator<(Lemma const &b) const { return this->score < b.score; }

    bool operator>(Lemma const &b) const { return this->score > b.score; }

    bool operator<=(Lemma const &b) const { return this->score <= b.score; }

    bool operator>=(Lemma const &b) const { return this->score >= b.score; }

    std::string smtlib;
};


#endif //CLAUSE_SERVER_SMTLITERAL_H
