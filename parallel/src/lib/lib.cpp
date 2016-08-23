//
// Created by Matteo on 11/08/16.
//

#include "lib.h"


void split(const std::string &string, const std::string &delimiter, std::vector<std::string> &vector) {
    return split(string, delimiter, [&vector](std::string &sub) {
        vector.push_back(sub);
    });
}


void split(const std::string &string, const std::string &delimiter, std::function<void(std::string &)> callback) {
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


void join(std::string &string,
          const std::string &delimiter,
          std::vector<std::string>::iterator first,
          std::vector<std::string>::iterator last) {
    for (; first != last; ++first) {
        string.append(*first);
        if (first + 1 != last)
            string.append(delimiter);
    }
}


void replace(std::string &string, const std::string &from, const std::string &to) {
    if (from.empty())
        return;
    size_t start_pos = 0;
    while ((start_pos = string.find(from, start_pos)) != std::string::npos) {
        string.replace(start_pos, from.length(), to);
        start_pos += to.length();
    }
}