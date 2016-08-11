//
// Created by Matteo on 11/08/16.
//

#include "lib.h"


void split(std::string &string, std::string delimiter, std::vector<std::string> &vector) {
    size_t b = 0;
    size_t e;
    while ((e = string.find(delimiter, b)) != std::string::npos) {
        vector.push_back(string.substr(b, e - b));
        b = e + delimiter.size();
    }
    vector.push_back(string.substr(b));
}

void split(std::string &string, std::string delimiter, std::function<void(std::string &)> callback) {
    size_t b = 0;
    size_t e;
    while ((e = string.find(delimiter, b)) != std::string::npos) {
        std::string sub = string.substr(b, e - b);
        callback(sub);
        b = e + delimiter.size();
    }
    //callback(string.substr(b));
}