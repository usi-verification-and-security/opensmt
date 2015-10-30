//
// Created by Matteo Marescotti.
//

#include "protocol.h"

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

void Message::dump(std::string &s) {
    std::map<std::string, std::string>::iterator it;

    for (it = this->header.begin(); it != this->header.end(); it++) {
        std::string keyval[2] = {it->first, it->second};
        for (uint8_t i = 0; i < 2; i++) {
            if (keyval[i].length() > ((1 << 8) - 1))
                throw "Header map's key or value too big";
            s += (uint8_t) keyval[i].length();
            s += keyval[i];
        }
    }

    s += '\0';

    s += this->payload;

};

void Message::load(std::string &s) {
    uint32_t i = 0;
    this->header.clear();
    while (s[i] != '\0') {
        if (i >= s.length())
            throw "load message error";
        std::string keyval[2] = {"", ""};
        for (uint8_t j = 0; j < 2; j++) {
            uint8_t l = (uint8_t) s[i++];
            keyval[j] += s.substr(i, l);
            i += l;
        }
        this->header[keyval[0]] = keyval[1];
    }
    i++;

    this->payload.clear();
    if (s.length() > i)
        this->payload.append(s.substr(i));

}


void clauseSerialize(Clause &c, std::string &s) {
    s.reserve(4 + 4 * c.size());
    int2str((uint32_t) c.size(), s);
    for (int i = 0; i < c.size(); i++) {
        int2str((uint32_t) toInt(c[i]), s);
    }
}

void clauseDeserialize(std::string &s, uint32_t *o, vec<Lit> &lits) {
    if (s.length() < *o + 4)
        return;
    uint32_t size = (uint32_t) str2int(s.substr(*o, 4), 4);
    *o += 4;
    if (s.length() < *o + (size * 4))
        return;
    for (uint32_t i = 0; i < size; i++) {
        lits.push(toLit((uint32_t) str2int(s.substr(*o, 4), 4)));
        *o += 4;
    }
    return;
}