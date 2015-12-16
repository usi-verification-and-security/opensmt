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


inline void int2str(uint8_t i, std::string &s) {
    s += (char) i;
}

inline uint64_t str2int(const std::string &s, uint8_t b = 4) {
    assert(b > 0 && b <= 8);
    assert(s.length() >= b);
    uint64_t i = 0;
    while (b-- > 0)
        i |= ((uint8_t) s[b]) << (b * 8);
    return i;
}

inline void int2str(uint32_t i, std::string &s) {
    s += (char) i;
    s += (char) (i >> 8);
    s += (char) (i >> 16);
    s += (char) (i >> 24);
}

template<typename T>
void clauseSerialize(T &lits, std::string &s) {
    if (lits.size() <= 0)
        return;
    s.reserve(s.size() + (unsigned) 4 + 4 * lits.size());
    int2str((uint32_t) lits.size(), s);
    for (int i = 0; i < lits.size(); i++) {
        int2str((uint32_t) toInt(lits[i]), s);
    }
}

void clauseDeserialize(std::string &s, uint32_t *o, vec<Lit> &lits);


#endif //CLAUSE_SHARING_PROTOCOL_H
