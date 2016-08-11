//
// Created by Matteo on 11/08/16.
//

#include "lib.h"


void split(std::string &string, std::string delimiter, std::vector<std::string> &vector) {
    return split(string, delimiter, [&vector](std::string &sub) {
        vector.push_back(sub);
    });
}

void split(std::string &string, std::string delimiter, std::function<void(std::string &)> callback) {
    size_t b = 0;
    size_t e;
    std::string sub;
    while (true) {
        e = string.find(delimiter, b);
        sub = string.substr(b, e - b);
        callback(sub);
        if (e == std::string::npos)
            return;
        b = e + delimiter.size();
    }
}