//
// Created by Matteo on 11/08/16.
//

#ifndef CLAUSE_SERVER_LIB_H
#define CLAUSE_SERVER_LIB_H

#include <string>
#include <vector>
#include <functional>


void split(std::string &, std::string, std::vector<std::string> &);

void split(std::string &, std::string, std::function<void(std::string &)>);

#endif //CLAUSE_SERVER_LIB_H
