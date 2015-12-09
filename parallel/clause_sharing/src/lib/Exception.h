//
// Created by Matteo on 09/12/15.
//

#ifndef CLAUSE_SHARING_EXCEPTION_H
#define CLAUSE_SHARING_EXCEPTION_H

#include <exception>


class Exception : public std::exception {
private:
    std::string msg;

public:
    explicit Exception(const char *message) :
            msg(message) { }

    explicit Exception(const std::string &message) :
            msg(message) { }

    char const *what() const throw() { return this->msg.c_str(); }
};

#endif //CLAUSE_SHARING_EXCEPTION_H
