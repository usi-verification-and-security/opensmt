//
// Created by Matteo on 11/08/16.
//

#ifndef CLAUSE_SERVER_LIB_H
#define CLAUSE_SERVER_LIB_H

#include <string>
#include <vector>
#include <functional>


void split(const std::string &, const std::string &, std::vector<std::string> &);

void split(const std::string &, const std::string &, std::function<void(std::string &)>);

void join(std::string &, const std::string &, std::vector<std::string>::iterator, std::vector<std::string>::iterator);

void replace(std::string &, const std::string &, const std::string &);

#endif //CLAUSE_SERVER_LIB_H
